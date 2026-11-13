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
#include "base/wlc/wlc.h"
#include "opt/ufar/UfarCmd.h"
#include "opt/drw/drw.h"
#include "opt/abs2/abs2.h"
#include "proof/pdr/pdr.h"
#include "proof/pdr2/pdr2.h"
#include "proof/imc/imc.h"
#include "proof/int/int.h"
#include "proof/ssw/ssw.h"
#include "proof/ssw/sswSim4.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satSolver.h"
#include <errno.h>
#include <limits.h>
#ifdef ABC_USE_CUDD
#include "bdd/llb/llb.h"
#endif

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
       SUPER_BMC3_CLASSIC, SUPER_BMC3_GLUCOSE, SUPER_RAR, SUPER_KIND, SUPER_SCORR3,
       SUPER_SCORR4, SUPER_SCORR, SUPER_GLA, SUPER_ABS, SUPER_DRWSAT,
       SUPER_PDR_T, SUPER_PDR_T_OR, SUPER_GLA_PDR, SUPER_GLA_PDR_ORIGINAL,
       SUPER_SCNEW, SUPER_PDR_T_SCORR, SUPER_RAR_SCNEW, SUPER_UFAR, SUPER_INT_OLD,
       SUPER_PDR2_T, SUPER_PDR2_QUICK, SUPER_PDR2_T_QUICK, SUPER_BMC3_CADICAL, SUPER_BMC3_CADICAL_GLUCOSE,
       SUPER_SIM4, SUPER_SYN2_SCORR, SUPER_RETIME_SCORR, SUPER_PDR2_SIM, SUPER_PDR2_SIM_QUICK,
       SUPER_PDR2_TEMPORAL, SUPER_GLA_TEMPORAL, SUPER_PDR2_RPM, SUPER_PHASE_SCORR, SUPER_INT_SYN2, SUPER_PDR2_STARTUP,
       SUPER_BDD_SIMPLIFY, SUPER_ENGINES, SUPER_COMB = SUPER_ENGINES, SUPER_QUEUE = 128 };

typedef struct Cec_SuperMan_t_ Cec_SuperMan_t;
typedef struct Cec_SuperWorker_t_ Cec_SuperWorker_t;
struct Cec_SuperMan_t_
{
    Gia_Man_t * pOriginal;
    Gia_Man_t * pInitial;
    Gia_Man_t * pStartup;
    Gia_Man_t * pBest;
    Gia_Man_t * pKind;
    Gia_Man_t * pCorr;
    Gia_Man_t * pPrepared[2];
    Wlc_Ntk_t * pWlc;
    Cec_ParSuper_t * pPars;
    Abc_Cex_t * pCex;
    abctime Start, Deadline, SolvedAt;
    int Result, Generation, Active, ActivePersistent, Head, Tail, Done, nWorkers;
    int Queue[SUPER_QUEUE];
    int Started[SUPER_ENGINES+1], Running[SUPER_ENGINES+1];
    int Deferred[SUPER_ENGINES+1], RetryBudget[SUPER_ENGINES+1];
    int fComb, fPersistentBmc, fPersistentPdr, fPersistentExtra, fEarlyAbs, fRpmEarly;
    int CorrState, CorrAttempts;
    int PrepareState[2], PrepareSteps[2];
    int StartupState;
    abctime PrepareLimit[2];
    int nBmcFrames;
    word DirectHash[8];
    abctime DirectBudget[8];
    int DirectFrames[8], DirectLimit[8], nDirectEntries;
    word RarSeedHash[8];
    int nRarSeedEntries;
    unsigned nRarRuns;
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
    Abc_Cex_t * pCheckedCex;
    abctime Deadline;
    int Id, Engine, Generation, Seconds, fInterrupted, fMerged, fPersistent, fRaw, fInitial;
    Vec_Int_t * vGlaClasses;
    int nGlaSeconds, fGlaSat;
    int RarSeed;
    int nDirectFrames;
    const char * pSolvedBy;
};
static ABC_THREAD_LOCAL Cec_SuperWorker_t * s_pSuperWorker = NULL;
static int Cec_SuperSolve( Cec_SuperWorker_t * pWorker );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Invalidates preparation eligibility when a worker changes graphs.]

  Description [Only the scheduler grants initial-model eligibility. Restoring
  a saved graph does not restore eligibility after a private transformation.]

  SideEffects [Assigns the worker graph without freeing the previous graph.]

  SeeAlso     [Cec_SuperNext Cec_SuperPrepare]

***********************************************************************/
static void Cec_SuperSetGia( Cec_SuperWorker_t * pWorker, Gia_Man_t * pGia )
{
    pWorker->pGia = pGia;
    pWorker->fInitial = 0;
}

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
    pPars->nBmcMemory = 8192;
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
        "auto", "pdr2", "fla", "int", "pdr", "bmc3-classic", "bmc3-glucose", "rar",
        "kind", "scorr3", "scorr4", "scorr", "gla", "abs", "drwsat",
        "pdr-t", "pdr-t-or", "gla-pdr", "gla-pdr-original",
        "scnew", "pdr-t-scorr", "rar-scnew", "ufar", "int-old", "pdr2-t",
        "pdr2-quick", "pdr2-t-quick", "bmc3-cadical", "bmc3-cadical-glucose", "sim4", "syn2-scorr",
        "retime-scorr", "pdr2-sim", "pdr2-sim-quick", "pdr2-temporal", "gla-temporal", "pdr2-rpm", "phase-scorr",
        "int-syn2", "pdr2-startup", "bdd-simplify" };
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
    if ( !strcmp(pName, "bmc") ) return SUPER_BMC3_CLASSIC;
    if ( !strcmp(pName, "bmc-g") ) return SUPER_BMC3_GLUCOSE;
    if ( !strcmp(pName, "bmc3") ) return SUPER_BMC3_CADICAL;
    if ( !strcmp(pName, "bmc3-g") ) return SUPER_BMC3_CADICAL_GLUCOSE;
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

  Synopsis    [Waits briefly for a shared model while retaining the caller's limit.]

  Description [The caller holds the scheduler mutex.]

  SideEffects [Releases and reacquires the mutex during the wait.]

  SeeAlso     [Cec_SuperPrepare Cec_SuperSharedCorr]

***********************************************************************/
static void Cec_SuperWait( Cec_SuperMan_t * p )
{
#ifdef SUPER_USE_PTHREADS
    struct timespec Wake;
    int Status;
#if defined(CLOCK_REALTIME)
    if ( clock_gettime(CLOCK_REALTIME, &Wake) )
    {
        Wake.tv_sec = time(NULL);
        Wake.tv_nsec = 0;
    }
    Wake.tv_nsec += 100000000;
    if ( Wake.tv_nsec >= 1000000000 ) { Wake.tv_sec++; Wake.tv_nsec -= 1000000000; }
#else
    Wake.tv_sec = time(NULL) + 1;
    Wake.tv_nsec = 0;
#endif
    Status = pthread_cond_timedwait( &p->Cond, &p->Mutex, &Wake );
    assert( Status == 0 || Status == ETIMEDOUT );
    (void)Status;
#else
    (void)p;
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

  Synopsis    [Reports a pipeline result under its public lane name.]

  Description [The inner engine remains available in verbose transcripts.]

  SideEffects []

  SeeAlso     [Cec_SuperReport]

***********************************************************************/
static void Cec_SuperLaneWinner( Cec_SuperWorker_t * pWorker, int Engine, int Result )
{
    if ( Result < 0 ) return;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: winning lane=%s inner=%s\n",
            Cec_ManSuperEngineName(Engine), pWorker->pSolvedBy );
    pWorker->pSolvedBy = Cec_ManSuperEngineName( Engine );
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

  Synopsis    [Exchanges safe prefixes between the two concrete BMC lanes.]

  Description [Both lanes use the initial model with the same reset and
  output semantics. Abstract, retimed and seeded simulations never share
  this context. A prefix is published only after all its outputs are refuted.]

  SideEffects [Updates the manager-owned prefix under its mutex.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperBmcFrames( void * pData, int nFrames )
{
    Cec_SuperMan_t * p = (Cec_SuperMan_t *)pData;
    int Result;
    Cec_SuperLock( p );
    if ( nFrames > p->nBmcFrames ) p->nBmcFrames = nFrames;
    Result = p->nBmcFrames;
    Cec_SuperUnlock( p );
    return Result;
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

  Synopsis    [Replays a candidate on the original graph, preserving PI order.]

  Description [All transformations keep PI order and zero initialization.
  Reconstructing the original register trajectory by simulation avoids using
  a reduced or abstract state as an original counterexample.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Cec_SuperCheckCex( Cec_SuperWorker_t * pWorker )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pCheck;
    Abc_Cex_t * pCex = NULL, * pSource = pWorker->pGia->pCexSeq;
    ABC_INT64_T nBits;
    int i;
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
    return pCex;
rejected:
    Abc_Print( 1, "Warning: super_prove rejected a counterexample from %s on the original graph.\n",
        pWorker->pSolvedBy );
    Abc_CexFreeP( &pCex );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Publishes a result after checking its candidate at most once.]

  Description [A rarity phase may check its candidate before returning so
  it can continue searching after a failed replay. The checked original
  trace stays with this worker until publication or cleanup.]

  SideEffects [Transfers ownership of the checked trace to the manager.]

  SeeAlso     [Cec_SuperCheckCex]

***********************************************************************/
static int Cec_SuperPublish( Cec_SuperWorker_t * pWorker, int Result )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Abc_Cex_t * pCex = NULL;
    int Accepted = 0;
    if ( Result != 0 && Result != 1 ) return 0;
    if ( Result == 0 )
    {
        pCex = pWorker->pCheckedCex ? pWorker->pCheckedCex : Cec_SuperCheckCex(pWorker);
        pWorker->pCheckedCex = NULL;
        if ( !pCex ) return 0;
    }
    Cec_SuperLock( p );
    if ( p->Result == -1 )
    {
        p->Result = Result;
        p->SolvedAt = Abc_Clock();
        p->pCex = pCex;
        pCex = NULL;
        p->pPars->pWinner = pWorker->pSolvedBy;
        Accepted = 1;
        Cec_SuperRequestStop( p );
    }
    Cec_SuperUnlock( p );
    Abc_CexFreeP( &pCex );
    return Accepted;
}

/**Function*************************************************************

  Synopsis    [Queues reduction follow-ups without starving initial strategies.]

  Description [Pending tasks use the latest model when dequeued. Active
  tasks keep their private model and are not removed. Caller holds Mutex.]

  SideEffects [Compacts the pending queue.]

  SeeAlso     [Cec_SuperReduce]

***********************************************************************/
static void Cec_SuperPrioritize( Cec_SuperMan_t * p, int fStrong )
{
    int Queue[SUPER_QUEUE], Follow[] = { SUPER_KIND, SUPER_SCORR, SUPER_PDR2, SUPER_PDR_T_OR };
    int i, nTasks = 0;
    for ( i = 0; i < 4; i++ )
        if ( (fStrong || i != 1) && p->Running[Follow[i]] && p->Started[Follow[i]] < p->Generation )
            p->Deferred[Follow[i]] = 1;
    for ( i = 0; i < (fStrong ? 4 : 1); i++ )
        if ( !p->Running[Follow[i]] && p->Started[Follow[i]] < p->Generation ) Queue[nTasks++] = Follow[i];
    if ( !fStrong )
    {
        // Give complementary initial searches a chance before another long proof.
        for ( i = p->Head; i < p->Tail; i++ )
            if ( p->Queue[i] == SUPER_RETIME_SCORR ) Queue[nTasks++] = p->Queue[i];
        for ( i = p->Head; i < p->Tail; i++ )
            if ( p->Queue[i] == SUPER_BMC3_CADICAL || p->Queue[i] == SUPER_SIM4 ||
                 p->Queue[i] == SUPER_SYN2_SCORR ) Queue[nTasks++] = p->Queue[i];
        for ( i = 2; i < 4; i++ )
            if ( !p->Running[Follow[i]] && p->Started[Follow[i]] < p->Generation ) Queue[nTasks++] = Follow[i];
    }
    for ( i = p->Head; i < p->Tail; i++ )
        if ( p->Queue[i] != SUPER_KIND && p->Queue[i] != SUPER_PDR2 && p->Queue[i] != SUPER_PDR_T_OR )
        {
            if ( fStrong && p->Queue[i] == SUPER_SCORR ) continue;
            if ( !fStrong && (p->Queue[i] == SUPER_BMC3_CADICAL || p->Queue[i] == SUPER_SIM4 ||
                 p->Queue[i] == SUPER_SYN2_SCORR || p->Queue[i] == SUPER_RETIME_SCORR) ) continue;
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
    ABC_INT64_T OldCost, NewCost;
    if ( !pNew ) return;
    if ( Gia_ManPiNum(pNew) != Gia_ManPiNum(p->pOriginal) ||
         Gia_ManPoNum(pNew) != Gia_ManPoNum(p->pOriginal) )
    {
        Gia_ManStop( pNew );
        return;
    }
    if ( !Gia_ManIsNormalized(pNew) )
    {
        Gia_Man_t * pNorm = Gia_ManDupNormalize( pNew, 1 );
        Gia_ManStop( pNew );
        pNew = pNorm;
    }
    Cec_SuperLock( p );
    OldCost = (ABC_INT64_T)Gia_ManAndNum(p->pBest) + 16 * (ABC_INT64_T)Gia_ManRegNum(p->pBest);
    NewCost = (ABC_INT64_T)Gia_ManAndNum(pNew) + 16 * (ABC_INT64_T)Gia_ManRegNum(pNew);
    if ( p->Result == -1 && NewCost < OldCost )
    {
        int Meaningful = 10 * NewCost <= 9 * OldCost ||
            10 * (ABC_INT64_T)Gia_ManRegNum(pNew) <= 9 * (ABC_INT64_T)Gia_ManRegNum(p->pBest);
        int Strong = 2 * NewCost <= OldCost ||
            2 * (ABC_INT64_T)Gia_ManRegNum(pNew) <= Gia_ManRegNum(p->pBest);
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
        // A completed correspondence pass has already processed its own result.
        if ( pWorker->Engine == SUPER_SCORR )
        {
            p->Started[SUPER_SCORR] = p->Generation;
            p->Deferred[SUPER_SCORR] = p->RetryBudget[SUPER_SCORR] = 0;
        }
        if ( Meaningful && !p->pPars->iEngine )
            Cec_SuperPrioritize( p, Strong );
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
    int Result, Seconds, fInterrupted = pWorker->fInterrupted;
    if ( Cec_SuperStop(pWorker) || !pGia->vGateClasses ) return -1;
    if ( pWorker->vGlaClasses && Vec_IntSize(pWorker->vGlaClasses) == Vec_IntSize(pGia->vGateClasses) &&
         !memcmp(Vec_IntArray(pWorker->vGlaClasses), Vec_IntArray(pGia->vGateClasses),
                 (size_t)Vec_IntSize(pGia->vGateClasses) * sizeof(int)) )
    {
        // A reachable bad state in this exact abstraction rules out a proof of it.
        // GLA still refines normally; an abstract trace is never a concrete answer.
        if ( pWorker->fGlaSat )
        {
            if ( pWorker->pMan->pPars->fVerbose )
                Abc_Print( 1, "super_prove: unchanged abstraction already SAT; continue refinement\n" );
            return -1;
        }
        pWorker->nGlaSeconds = Abc_MinInt( 32, 2 * pWorker->nGlaSeconds );
    }
    else
    {
        Vec_IntFreeP( &pWorker->vGlaClasses );
        pWorker->vGlaClasses = Vec_IntDup( pGia->vGateClasses );
        pWorker->nGlaSeconds = 2;
        pWorker->fGlaSat = 0;
    }
    Seconds = pWorker->nGlaSeconds;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: stable abstraction proof budget=%d sec\n", Seconds );
    vClasses = Vec_IntDup( pGia->vGateClasses );
    pAbs = Gia_ManDupAbsGates( pGia, vClasses );
    Vec_IntFree( vClasses );
    Gia_ManCleanValue( pGia );
    pAbs = Gia_ManDupNormalize( pTemp = pAbs, 1 );
    Gia_ManStop( pTemp );
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    // Give a stable abstraction a longer proof attempt before more unrolling.
    if ( Deadline - Now > Seconds * (abctime)CLOCKS_PER_SEC )
        pWorker->Deadline = Now + Seconds * (abctime)CLOCKS_PER_SEC;
    Pdr_ManSetDefaultParams( &Pars );
    Pars.nTimeOut = Seconds;
    Pars.fTsimStop = 1;
    Pars.fSilent = 1;
    Pars.pFuncStop = Cec_SuperStopId;
    Now = Abc_Clock();
    Result = Pdr_ManSolve( pAig, &Pars );
    pWorker->fGlaSat = Result == 0;
    Aig_ManStop( pAig );
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: abstraction proof result=%d budget=%d elapsed=%.6f sec\n",
            Result, Seconds, (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = fInterrupted;
    return Result == 1 ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Computes the initial correspondence model once for both pipelines.]

  Description [The cached graph is immutable except during serialized copies.
  Only a completed reduction is retained; an interrupted pass is discarded.]

  SideEffects [Signals waiting workers when the shared pass finishes.]

  SeeAlso     [Cec_SuperCorrRace]

***********************************************************************/
static int Cec_SuperSharedCorr( Cec_SuperWorker_t * pWorker, abctime Limit )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pNew = NULL;
    abctime WaitLimit = pWorker->Deadline < Limit ? pWorker->Deadline : Limit;
    int Result;
    Cec_SuperLock( p );
#ifdef SUPER_USE_PTHREADS
    while ( p->CorrState == 1 && p->Result == -1 && Abc_Clock() < WaitLimit )
        Cec_SuperWait( p );
#endif
    if ( p->Result != -1 || Abc_Clock() >= WaitLimit )
    {
        Cec_SuperUnlock( p );
        return -1;
    }
    if ( p->CorrState == 2 )
    {
        if ( p->pCorr ) pNew = Gia_ManDup( p->pCorr );
        Cec_SuperUnlock( p );
        if ( pNew ) { Gia_ManStop(pWorker->pGia); Cec_SuperSetGia( pWorker, pNew ); }
        return Cec_SuperConstant( pWorker->pGia );
    }
    p->CorrState = 1;
    pWorker->Deadline = Abc_Clock() + (abctime)(p->CorrAttempts++ ? 10 : 3) * CLOCKS_PER_SEC;
    if ( pWorker->Deadline > Limit ) pWorker->Deadline = Limit;
    pWorker->Seconds = Abc_MaxInt( 1, (int)((pWorker->Deadline - Abc_Clock() +
        CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
    Cec_SuperUnlock( p );
    Result = Cec_SuperSolve( pWorker );
    if ( !pWorker->fInterrupted && Result < 0 ) pNew = Gia_ManDup( pWorker->pGia );
    Cec_SuperLock( p );
    p->pCorr = pNew;
    p->CorrState = pWorker->fInterrupted && p->CorrAttempts < 2 &&
        Gia_ManRegNum(p->pInitial) <= 2048 && Gia_ManAndNum(p->pInitial) < 100000 ? 0 : 2;
    Cec_SuperWake( p );
    Cec_SuperUnlock( p );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries independent properties without changing the deeper model.]

  Description [A cheap correspondence pass can make separate properties easy
  even when their disjunction remains difficult. Keep this bounded attempt
  private so an unfinished proof does not change the established pipeline.]

  SideEffects [Retains the private model only when it yields a verdict.]

  SeeAlso     [Cec_SuperCorrRace]

***********************************************************************/
static int Cec_SuperCorrProbe( Cec_SuperWorker_t * pWorker )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pSaved = pWorker->pGia, * pProbe, * pNew, * pTemp;
    Cec_ParCor_t Pars;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Engine = pWorker->Engine, Seconds = pWorker->Seconds;
    int fMerged = pWorker->fMerged, Result = -1;
    Cec_SuperLock( p );
    pProbe = Gia_ManDup( p->pInitial );
    Cec_SuperUnlock( p );
    pWorker->Deadline = Start + 3 * (abctime)CLOCKS_PER_SEC;
    if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    Cec_ManCorSetDefaultParams( &Pars );
    Pars.nProcs = 1;
    Pars.nBTLimit = 100;
    Pars.nLevelMax = 100;
    Pars.pFunc = (void *)Cec_SuperStop;
    Pars.pData = pWorker;
    pNew = Cec_ManLSCorrespondence( pProbe, &Pars );
    Gia_ManStop( pProbe );
    if ( pNew && !pWorker->fInterrupted )
    {
        pProbe = Gia_ManDupNormalize( pTemp = pNew, 1 );
        Gia_ManStop( pTemp );
        pNew = NULL;
        Cec_SuperSetGia( pWorker, pProbe );
        pWorker->fMerged = 0;
        pWorker->Deadline = Abc_Clock() + 2 * (abctime)CLOCKS_PER_SEC;
        if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
        pWorker->Seconds = 2;
        pWorker->Engine = SUPER_PDR_T;
        Result = Cec_SuperSolve( pWorker );
        if ( Result >= 0 ) Gia_ManStop( pSaved );
        else Gia_ManStop( pProbe );
    }
    Gia_ManStopP( &pNew );
    if ( Result < 0 )
    {
        Cec_SuperSetGia( pWorker, pSaved );
        pWorker->fMerged = fMerged;
    }
    pWorker->Engine = Engine;
    pWorker->Deadline = Deadline;
    pWorker->Seconds = Seconds;
    pWorker->fInterrupted = 0;
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "super_prove: separate-property probe result=%d elapsed=%.3f sec\n",
            Result, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Races a classical correspondence model on the current worker.]

  Description [Keeps the solver model separate from combinational rewriting.
  Each reduction has its own bounded slice within the worker's deadline.]

  SideEffects [May publish completed reductions for other workers.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperCorrRace( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pSaved;
    abctime Deadline = pWorker->Deadline, Now, Budget, Start;
    int Engine = pWorker->Engine, Seconds = pWorker->Seconds, RarSeed = pWorker->RarSeed;
    int i, Result = -1, nSteps = Engine == SUPER_PDR_T_SCORR ? 2 : 1;
    int fInitial = pWorker->fInitial;
    int nCorrMin = pWorker->pMan->nWorkers >= 6 && Seconds >= 15 ? 6 : 1;
    pWorker->fRaw = 1;
    if ( Gia_ManPoNum(pWorker->pGia) > 1 )
    {
        Gia_Man_t * pNew = Cec_SuperMergeOutputs( pWorker->pGia );
        Gia_ManStop( pWorker->pGia );
        Cec_SuperSetGia( pWorker, pNew );
        pWorker->fMerged = 1;
    }
    if ( Engine == SUPER_RAR_SCNEW && !Cec_SuperStop(pWorker) )
    {
        // Retain the quick simulation opportunity before sequential reduction.
        pSaved = pWorker->pGia;
        Cec_SuperLock( pWorker->pMan );
        Cec_SuperSetGia( pWorker, Gia_ManDup(pWorker->pMan->pBest) );
        Cec_SuperUnlock( pWorker->pMan );
        Now = Abc_Clock();
        pWorker->Deadline = Now + CLOCKS_PER_SEC;
        if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
        pWorker->Seconds = 1;
        pWorker->Engine = SUPER_RAR;
        pWorker->RarSeed = (RarSeed + 113) % 1000;
        Result = Cec_SuperSolve( pWorker );
        pWorker->RarSeed = RarSeed;
        pWorker->Deadline = Deadline;
        pWorker->Seconds = Seconds;
        pWorker->fInterrupted = 0;
        if ( Result >= 0 )
        {
            Gia_ManStop( pSaved );
            goto finish;
        }
        Gia_ManStop( pWorker->pGia );
        Cec_SuperSetGia( pWorker, pSaved );
    }
    for ( i = 0; i < nSteps && !Cec_SuperStop(pWorker); i++ )
    {
        if ( !Gia_ManRegNum(pWorker->pGia) ||
             (i && (Gia_ManAndNum(pWorker->pGia) >= 100000 || !Gia_ManPiNum(pWorker->pGia))) )
            break;
        Now = Start = Abc_Clock();
        Budget = (abctime)(i ? (pWorker->fPersistent || pWorker->pMan->pPars->iEngine ?
            Abc_MinInt(120, Abc_MaxInt(30, 3 * Seconds / 4)) : Abc_MaxInt(nCorrMin, Seconds / 3)) : 3) * CLOCKS_PER_SEC;
        if ( Budget > Deadline - Now ) Budget = Deadline - Now;
        pWorker->Deadline = Now + Budget;
        pWorker->Seconds = Abc_MaxInt( 1, (int)((Budget + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
        pWorker->fInterrupted = 0;
        pWorker->Engine = i ? SUPER_SCORR : SUPER_SCNEW;
        Result = i || !fInitial ? Cec_SuperSolve(pWorker) : Cec_SuperSharedCorr(pWorker, Deadline);
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: preprocess engine=%s and=%d ff=%d stopped=%d elapsed=%.3f sec\n",
                Cec_ManSuperEngineName(pWorker->Engine), Gia_ManAndNum(pWorker->pGia),
                Gia_ManRegNum(pWorker->pGia), pWorker->fInterrupted,
                (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
        pWorker->Deadline = Deadline;
        pWorker->Seconds = Seconds;
        pWorker->fInterrupted = 0;
        if ( Result >= 0 ) break;
        if ( !i && Engine == SUPER_PDR_T_SCORR && pWorker->fPersistent &&
             !pWorker->pMan->pPars->iEngine && Gia_ManPoNum(pWorker->pMan->pInitial) > 1 &&
             10 * (ABC_INT64_T)Gia_ManRegNum(pWorker->pGia) <=
             9 * (ABC_INT64_T)Gia_ManRegNum(pWorker->pMan->pInitial) && !Cec_SuperStop(pWorker) )
        {
            Result = Cec_SuperCorrProbe( pWorker );
            if ( Result >= 0 ) break;
        }
    }
    if ( Result < 0 && !Cec_SuperStop(pWorker) )
    {
        int fConcreteFallback = Engine == SUPER_PDR_T_SCORR &&
            !pWorker->pMan->pPars->iEngine && pWorker->fPersistent &&
            Deadline - Abc_Clock() >= 120 * (abctime)CLOCKS_PER_SEC;
        pWorker->Engine = Engine == SUPER_PDR_T_SCORR ? SUPER_PDR_T : SUPER_RAR;
        if ( fConcreteFallback )
        {
            // Keep a long concrete proof on the completed correspondence model.
            pWorker->Deadline = Abc_Clock() + 30 * (abctime)CLOCKS_PER_SEC;
            if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
            pWorker->Seconds = 30;
        }
        Result = Cec_SuperSolve( pWorker );
        if ( fConcreteFallback )
        {
            pWorker->Deadline = Deadline;
            pWorker->fInterrupted = 0;
            pWorker->Seconds = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() +
                CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
            if ( Result < 0 && !Cec_SuperStop(pWorker) )
            {
                if ( pWorker->pMan->pPars->fVerbose )
                    Abc_Print( 1, "super_prove: correspondence fallback to concrete PDR.\n" );
                pWorker->Engine = SUPER_PDR;
                Result = Cec_SuperSolve( pWorker );
            }
        }
    }
finish:
    pWorker->Engine = Engine;
    pWorker->fRaw = 0;
    Cec_SuperLaneWinner( pWorker, Engine, Result );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Shares bounded preparation of identical initial models.]

  Description [Each retained graph contains only completed steps and preserves
  the input/output order. A later caller can resume an unfinished recipe with
  a longer slice, bounded by its own deadline. Transformed models are prepared
  privately. Cache copies and replacements are serialized.]

  SideEffects [May populate an immutable per-run cache and wake waiting workers.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperPrepare( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker,
    int fSyn2, int nSeconds, int fForceSyn2 )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pModel = NULL, * pNext;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock(), Budget, StepLimit = 0;
    int i = 0, fSynthesis = p->pPars->fRewrite || fForceSyn2;
    int Recipe = fSyn2 && fSynthesis;
    int fCache = !p->pPars->iEngine && pWorker->fInitial && pGia == pWorker->pGia;
    assert( nSeconds > 0 && (!fForceSyn2 || fSyn2) );
    if ( pGia == pWorker->pGia ) pWorker->fInitial = 0;
    Budget = nSeconds * (abctime)CLOCKS_PER_SEC;
    if ( fCache )
    {
        Cec_SuperLock( p );
#ifdef SUPER_USE_PTHREADS
        while ( p->PrepareState[Recipe] == 1 && p->Result == -1 && Abc_Clock() < Deadline )
            Cec_SuperWait( p );
#endif
        if ( p->Result != -1 || Abc_Clock() >= Deadline )
        {
            Cec_SuperUnlock( p );
            return Gia_ManDup( pGia );
        }
        if ( p->pPrepared[Recipe] )
        {
            pModel = Gia_ManDup( p->pPrepared[Recipe] );
            i = p->PrepareSteps[Recipe];
            if ( i == 3 || Deadline - Abc_Clock() <= p->PrepareLimit[Recipe] )
            {
                Cec_SuperUnlock( p );
                return pModel;
            }
            // Resume at the unfinished step instead of repeating completed work.
            if ( Budget < 2 * p->PrepareLimit[Recipe] ) Budget = 2 * p->PrepareLimit[Recipe];
        }
        p->PrepareState[Recipe] = 1;
        Cec_SuperUnlock( p );
    }
    if ( !pModel ) pModel = Gia_ManDup( pGia );
    Start = Abc_Clock();
    if ( Deadline - Start > Budget ) pWorker->Deadline = Start + Budget;
    for ( ; i < 3 && !Cec_SuperStop(pWorker); i++ )
    {
        if ( i == 1 && !fSynthesis ) { StepLimit = 0; continue; }
        StepLimit = pWorker->Deadline - Abc_Clock();
        pNext = i != 1 ? Gia_ManSeqStructSweepWithStop(pModel, 1, 1, 0, Cec_SuperStop, pWorker) :
            fSyn2 ? Gia_ManAigSyn2WithStop(pModel, Cec_SuperStop, pWorker) :
            Drw_ManRwsatWithStop(pModel, 0, 0, Cec_SuperStop, pWorker);
        if ( !pNext || pWorker->fInterrupted )
        {
            Gia_ManStopP( &pNext );
            break;
        }
        Gia_ManStop( pModel );
        pModel = pNext;
        StepLimit = 0;
    }
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    if ( fCache )
    {
        Cec_SuperLock( p );
        // Every retained step completed; a partial step never enters the cache.
        Gia_ManStopP( &p->pPrepared[Recipe] );
        p->pPrepared[Recipe] = Gia_ManDup( pModel );
        p->PrepareSteps[Recipe] = i;
        p->PrepareLimit[Recipe] = StepLimit;
        p->PrepareState[Recipe] = 2;
        Cec_SuperWake( p );
        Cec_SuperUnlock( p );
        if ( p->pPars->fVerbose )
            Abc_Print( 1, "super_prove: shared preparation=%s steps=%d/3 ff=%d and=%d elapsed=%.3f sec\n",
                fSynthesis ? (fSyn2 ? "syn2" : "drwsat") : "sweep", i,
                Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
                (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    }
    return pModel;
}

/**Function*************************************************************

  Synopsis    [Runs PDR2 after bounded structural simplification.]

  Description [Initial-model preprocessing is shared with equivalent lanes.]

  SideEffects [Replaces only this worker's private graph.]

  SeeAlso     [Cec_SuperPrepare Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperQuickPdr( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pNew;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Result, Engine = pWorker->Engine, Seconds = pWorker->Seconds;
    if ( Gia_ManObjNum(pWorker->pGia) <= 1000000 )
    {
        pNew = Cec_SuperPrepare( pWorker->pGia, pWorker, 0, 2, 0 );
        Gia_ManStop( pWorker->pGia );
        Cec_SuperSetGia( pWorker, pNew );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: private sweep and=%d ff=%d elapsed=%.3f sec\n",
                Gia_ManAndNum(pWorker->pGia), Gia_ManRegNum(pWorker->pGia),
                (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    }
    else if ( !pWorker->pMan->pPars->iEngine && pWorker->fInitial && pWorker->pMan->pStartup )
    {
        Cec_SuperLock( pWorker->pMan );
        pNew = Gia_ManDup( pWorker->pMan->pStartup );
        Cec_SuperUnlock( pWorker->pMan );
        Gia_ManStop( pWorker->pGia );
        Cec_SuperSetGia( pWorker, pNew );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: large-model startup copy and=%d ff=%d\n",
                Gia_ManAndNum(pNew), Gia_ManRegNum(pNew) );
    }
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    // Round up because the callback already enforces the precise deadline.
    pWorker->Seconds = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
    pWorker->Engine = Engine == SUPER_PDR2_QUICK ? SUPER_PDR2 :
        Engine == SUPER_PDR2_SIM_QUICK ? SUPER_PDR2_SIM : SUPER_PDR2_T;
    Result = Cec_SuperSolve( pWorker );
    pWorker->Engine = Engine;
    pWorker->Seconds = Seconds;
    Cec_SuperLaneWinner( pWorker, Engine, Result );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Represents the states reachable after a fixed initial prefix.]

  Description [Extra primary inputs describe the prefix from zero. A reset
  register selects its final state only in the first frame. Later frames use
  the ordinary transition relation. The caller separately proves the prefix.]

  SideEffects [Uses Value in the worker's private input graph.]

  SeeAlso     [Cec_SuperTemporalSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperTemporalModel( Cec_SuperWorker_t * pWorker, int Prefix )
{
    Gia_Man_t * pGia = pWorker->pGia, * pNew = NULL, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPis = NULL, * vRegs = NULL, * vState = NULL, * vNext = NULL;
    int i, f, Reset;
    if ( Prefix < 1 || Prefix > 2048 || !Gia_ManRegNum(pGia) || pGia->nConstrs ||
         (ABC_INT64_T)Gia_ManObjNum(pGia) * (Prefix + 2) > 10000000 ) return NULL;
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    pNew->pName = Abc_UtilStrsav( pGia->pName );
    vPis = Vec_IntAlloc( Gia_ManPiNum(pGia) * (Prefix + 1) );
    vRegs = Vec_IntAlloc( Gia_ManRegNum(pGia) );
    vState = Vec_IntStart( Gia_ManRegNum(pGia) );
    vNext = Vec_IntStart( Gia_ManRegNum(pGia) );
    for ( i = 0; i < Gia_ManPiNum(pGia) * (Prefix + 1); i++ )
        Vec_IntPush( vPis, Gia_ManAppendCi(pNew) );
    for ( i = 0; i < Gia_ManRegNum(pGia); i++ )
        Vec_IntPush( vRegs, Gia_ManAppendCi(pNew) );
    Reset = Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    for ( f = 0; f <= Prefix; f++ )
    {
        if ( Cec_SuperStop(pWorker) ) goto interrupted;
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachPi( pGia, pObj, i )
            pObj->Value = Vec_IntEntry(vPis, (f == Prefix ? 0 : f + 1) * Gia_ManPiNum(pGia) + i);
        Gia_ManForEachRo( pGia, pObj, i )
            pObj->Value = f == Prefix ? Gia_ManHashMux(pNew, Reset,
                Vec_IntEntry(vRegs, i), Vec_IntEntry(vState, i)) : Vec_IntEntry(vState, i);
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto interrupted;
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        if ( f < Prefix )
        {
            Gia_ManForEachRi( pGia, pObj, i )
                Vec_IntWriteEntry( vNext, i, Gia_ObjFanin0Copy(pObj) );
            ABC_SWAP( Vec_Int_t *, vState, vNext );
        }
    }
    Gia_ManForEachPo( pGia, pObj, i ) Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachRi( pGia, pObj, i ) Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManAppendCo( pNew, 1 );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) + 1 );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew ); Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 1 ); Gia_ManStop( pTemp );
    goto cleanup;
interrupted:
    Gia_ManStopP( &pNew );
cleanup:
    Vec_IntFreeP( &vPis ); Vec_IntFreeP( &vRegs ); Vec_IntFreeP( &vState ); Vec_IntFreeP( &vNext );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Restores prefix inputs in a temporal counterexample.]

  Description [The first frame's history inputs precede the current inputs
  from all later frames. Publication replays this candidate on the original
  graph. Invalid dimensions return NULL without reading the trace data.]

  SideEffects [Allocates a candidate owned by the caller.]

  SeeAlso     [Cec_SuperCheckCex]

***********************************************************************/
static Abc_Cex_t * Cec_SuperTemporalCex( Gia_Man_t * pGia, Abc_Cex_t * pSource, int Prefix )
{
    Abc_Cex_t * pCex;
    ABC_INT64_T nBits, nSourceBits;
    int f, i, Pi = Gia_ManPiNum(pGia), Bit;
    if ( !pSource || Prefix < 1 || Prefix > 2048 || pSource->iFrame < 0 ||
         pSource->iFrame > INT_MAX - Prefix - 1 || pSource->nRegs < 0 ||
         pSource->nPis != (ABC_INT64_T)Pi * (Prefix + 1) ||
         pSource->iPo < 0 || pSource->iPo >= Gia_ManPoNum(pGia) ) return NULL;
    nBits = (ABC_INT64_T)(pSource->iFrame + Prefix + 1) * Pi + Gia_ManRegNum(pGia);
    nSourceBits = (ABC_INT64_T)(pSource->iFrame + 1) * pSource->nPis + pSource->nRegs;
    if ( nBits > INT_MAX - 32 || nSourceBits > pSource->nBits ) return NULL;
    pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), Pi, pSource->iFrame + Prefix + 1 );
    pCex->iFrame = pSource->iFrame + Prefix;
    pCex->iPo = pSource->iPo;
    Bit = pCex->nRegs;
    for ( f = 0; f < Prefix; f++ )
        for ( i = 0; i < Pi; i++, Bit++ )
            if ( Abc_InfoHasBit(pSource->pData, pSource->nRegs + (f + 1) * Pi + i) )
                Abc_InfoSetBit( pCex->pData, Bit );
    for ( f = 0; f <= pSource->iFrame; f++ )
        for ( i = 0; i < Pi; i++, Bit++ )
            if ( Abc_InfoHasBit(pSource->pData, pSource->nRegs + f * pSource->nPis + i) )
                Abc_InfoSetBit( pCex->pData, Bit );
    assert( Bit == pCex->nBits );
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Recovers original inputs for a reparameterized state sequence.]

  Description [A one-frame SAT relation reconstructs one transition at a
  time. Only two simulation states are stored. The result is still replayed
  on the original portfolio input before publication.]

  SideEffects [Uses the worker's cancellation callback.]

  SeeAlso     [Cec_SuperRpm]

***********************************************************************/
static Abc_Cex_t * Cec_SuperRpmCex( Cec_SuperWorker_t * pWorker,
    Gia_Man_t * pBefore, Gia_Man_t * pAfter, Abc_Cex_t * pSource )
{
    sat_solver * pSat = NULL;
    Vec_Int_t * vAssumps = NULL;
    Abc_Cex_t * pCex = NULL;
    unsigned char * pValues = NULL, * pNext = NULL;
    Gia_Obj_t * pObj;
    ABC_INT64_T nBits;
    int i, f, Status, Bit, nRegs = Gia_ManRegNum(pAfter);
    if ( !pSource || pSource->iFrame < 0 || pSource->iFrame == INT_MAX ||
         pSource->nRegs < 0 || pSource->nPis != Gia_ManPiNum(pAfter) ||
         pSource->iPo < 0 || pSource->iPo >= Gia_ManPoNum(pAfter) ||
         Gia_ManPoNum(pBefore) != Gia_ManPoNum(pAfter) || Gia_ManRegNum(pBefore) != nRegs ) return NULL;
    nBits = (ABC_INT64_T)(pSource->iFrame + 1) * pSource->nPis + pSource->nRegs;
    if ( nBits > pSource->nBits || nBits < 0 ||
         (ABC_INT64_T)(pSource->iFrame + 1) * Gia_ManPiNum(pBefore) + nRegs > INT_MAX - 32 ) return NULL;
    if ( Cec_SuperStop(pWorker) ) return NULL;
    pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pAfter) );
    pNext = ABC_CALLOC( unsigned char, Abc_MaxInt(1, nRegs) );
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, Gia_ManObjNum(pBefore) );
    sat_solver_set_stop_func( pSat, Cec_SuperStopId );
    sat_solver_set_runtime_limit( pSat, pWorker->Deadline );
    sat_solver_add_const( pSat, 0, 1 );
    Gia_ManForEachAnd( pBefore, pObj, i )
    {
        if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto failed;
        sat_solver_add_and( pSat, i, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninId1(pObj, i),
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
    }
    pCex = Abc_CexAlloc( nRegs, Gia_ManPiNum(pBefore), pSource->iFrame + 1 );
    pCex->iFrame = pSource->iFrame;
    pCex->iPo = pSource->iPo;
    vAssumps = Vec_IntAlloc( 2 * nRegs + 1 );
    Bit = pCex->nRegs;
    for ( f = 0; f <= pSource->iFrame; f++ )
    {
        if ( Cec_SuperStop(pWorker) ) goto failed;
        Vec_IntClear( vAssumps );
        Gia_ManForEachRo( pBefore, pObj, i )
            Vec_IntPush( vAssumps, Abc_Var2Lit(Gia_ObjId(pBefore, pObj),
                !pValues[Gia_ObjId(pAfter, Gia_ManRo(pAfter, i))]) );
        Gia_ManForEachPi( pAfter, pObj, i )
            pValues[Gia_ObjId(pAfter, pObj)] =
                Abc_InfoHasBit(pSource->pData, pSource->nRegs + f * pSource->nPis + i);
        Gia_ManForEachAnd( pAfter, pObj, i )
        {
            if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto failed;
            pValues[i] = (pValues[Gia_ObjFaninId0(pObj, i)] ^ Gia_ObjFaninC0(pObj)) &
                (pValues[Gia_ObjFaninId1(pObj, i)] ^ Gia_ObjFaninC1(pObj));
        }
        Gia_ManForEachRi( pAfter, pObj, i )
            pNext[i] = pValues[Gia_ObjFaninId0p(pAfter, pObj)] ^ Gia_ObjFaninC0(pObj);
        if ( f < pSource->iFrame )
        {
            Gia_ManForEachRi( pBefore, pObj, i )
                Vec_IntPush( vAssumps, Gia_ObjFaninLit0p(pBefore, pObj) ^ !pNext[i] );
        }
        else
        {
            pObj = Gia_ManPo( pAfter, pSource->iPo );
            if ( !(pValues[Gia_ObjFaninId0p(pAfter, pObj)] ^ Gia_ObjFaninC0(pObj)) ) goto failed;
            Vec_IntPush( vAssumps, Gia_ObjFaninLit0p(pBefore, Gia_ManPo(pBefore, pSource->iPo)) );
        }
        Status = sat_solver_solve( pSat, Vec_IntArray(vAssumps),
            Vec_IntArray(vAssumps) + Vec_IntSize(vAssumps), 0, 0, 0, 0 );
        if ( Status != l_True ) goto failed;
        Gia_ManForEachPi( pBefore, pObj, i )
            if ( sat_solver_var_value(pSat, Gia_ObjId(pBefore, pObj)) )
                Abc_InfoSetBit( pCex->pData, Bit + i );
        Bit += Gia_ManPiNum(pBefore);
        Gia_ManForEachRo( pAfter, pObj, i ) pValues[Gia_ObjId(pAfter, pObj)] = pNext[i];
    }
    assert( Bit == pCex->nBits );
    goto cleanup;
failed:
    Abc_CexFreeP( &pCex );
cleanup:
    Vec_IntFreeP( &vAssumps );
    if ( pSat ) sat_solver_delete( pSat );
    ABC_FREE( pValues );
    ABC_FREE( pNext );
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Complements plain PDR2 with structural input reparameterization.]

  Description [Only this private model changes its primary inputs. SAT
  traces are reconstructed before the usual original-model replay.]

  SideEffects [May attach a reconstructed trace to the worker's graph.]

  SeeAlso     [Cec_SuperRpmCex]

***********************************************************************/
static int Cec_SuperRpm( Cec_SuperWorker_t * pWorker, int fUseAbs, int nObjLimit, int fUseBdd )
{
    Gia_Man_t * pModel = NULL, * pNext, * pBefore = NULL;
    Aig_Man_t * pAig = NULL;
    Pdr2_Par_t Pars;
    Abc_Cex_t * pCex;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock(), Now;
    int Result = -1;
    if ( Gia_ManObjNum(pWorker->pGia) > nObjLimit ) return -1;
    pModel = Cec_SuperPrepare( pWorker->pGia, pWorker, 0, 2, 0 );
    if ( Cec_SuperStop(pWorker) || Gia_ManObjNum(pModel) > nObjLimit ) goto done;
    if ( Gia_ManPiNum(pModel) )
    {
        Now = Abc_Clock();
        if ( Deadline - Now > 2 * (abctime)CLOCKS_PER_SEC )
            pWorker->Deadline = Now + 2 * (abctime)CLOCKS_PER_SEC;
        pBefore = Gia_ManDup( pModel );
        pNext = Abs_RpmPerformWithStop( pModel, 16, 0, 0, Cec_SuperStop, pWorker );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( pNext ) { Gia_ManStop(pModel); pModel = pNext; }
        else
        {
            Gia_ManStopP( &pBefore );
            if ( pWorker->pMan->pPars->fVerbose )
                Abc_Print( 1, "super_prove: reparameterization unfinished; using the simplified model.\n" );
        }
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: reparameterized pi=%d ff=%d and=%d elapsed=%.3f sec\n",
            Gia_ManPiNum(pModel), Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( Cec_SuperStop(pWorker) ) goto done;
    Pdr2_ManSetDefaultParams( &Pars );
    Pars.nTimeOut = Abc_MaxInt(1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC));
    Pars.pFuncStop = Cec_SuperStopId;
    Pars.fSilent = 1;
    Pars.nAbsRuns = Pars.nBmcTime = 0;
    Pars.fVerifyComplete = 1;
    if ( !pWorker->pMan->pPars->iEngine && pWorker->Engine == SUPER_PDR2_RPM )
        Pars.nRandomSeed = (191 + 37 * pWorker->Generation) % 1000;
    if ( fUseAbs ) Pars.fUseAbs = Pars.fBlockInduct = 1;
    pAig = Gia_ManToAigSimple( pModel );
#ifdef ABC_USE_CUDD
    if ( fUseBdd && Saig_ManRegNum(pAig) && Saig_ManRegNum(pAig) <= 256 )
    {
        Gia_ParLlb_t Llb;
        Llb_ManSetDefaultParams( &Llb );
        Llb.fCluster = Llb.fReorder = 0;
        Llb.nBddMax = 100;
        Llb.nClusterMax = 500;
        Llb.TimeLimit = 2;
        Llb.fSilent = 1;
        Now = Abc_Clock();
        if ( Deadline - Now > 2 * (abctime)CLOCKS_PER_SEC )
            pWorker->Deadline = Now + 2 * (abctime)CLOCKS_PER_SEC;
        Result = Llb_Nonlin4ProofWithStop( pAig, &Llb, Cec_SuperStop, pWorker, 512UL * 1024 * 1024 );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: bdd result=%d frames=%d elapsed=%.3f sec\n",
                Result, Llb.iFrame, (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC );
    }
#else
    (void)fUseBdd;
#endif
    if ( Result != 1 && !Cec_SuperStop(pWorker) )
    {
        Pars.nTimeOut = Abc_MaxInt(1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC));
        Result = Pdr2_ManSolve( pAig, &Pars );
    }
    if ( Result == 0 )
    {
        // Input reconstruction is a SAT search: allow at most one extra second
        // for a just-found trace, while still stopping when another lane wins.
        Now = Abc_Clock();
        if ( pWorker->Deadline < Now + CLOCKS_PER_SEC ) pWorker->Deadline = Now + CLOCKS_PER_SEC;
        if ( pBefore ) pCex = Cec_SuperRpmCex( pWorker, pBefore, pModel, pAig->pSeqModel );
        else { pCex = pAig->pSeqModel; pAig->pSeqModel = NULL; }
        pWorker->Deadline = Deadline;
        if ( pCex )
        {
            Abc_CexFreeP( &pWorker->pGia->pCexSeq );
            pWorker->pGia->pCexSeq = pCex;
        }
        else
        {
            if ( !pWorker->fInterrupted && !Cec_SuperReadStop(pWorker->pMan) )
                Abc_Print( 1, "Warning: super_prove could not reconstruct a counterexample from pdr2-rpm.\n" );
            Result = -1;
        }
    }
done:
    pWorker->Deadline = Deadline;
    Gia_ManStopP( &pBefore );
    if ( pAig ) Aig_ManStop( pAig );
    Gia_ManStop( pModel );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Selects a bounded full period or one of its smaller factors.]

  Description [The bounded simulation only selects a transformation. Every
  intermediate output remains in the transformed verification problem. Small
  complete periods can expose constant state after folding.]

  SideEffects []

  SeeAlso     [Cec_SuperPhaseSolve]

***********************************************************************/
static int Cec_SuperPhasePeriod( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker )
{
    const int Bins = 4093;
    unsigned char * pValues, * pStates, * pNext;
    int * pHeads, * pLinks;
    Gia_Obj_t * pObj;
    int i, f, k, a, b, Regs = Gia_ManRegNum(pGia), Limit, Prefix = 1;
    unsigned Hash;
    if ( !Regs ) return 0;
    Limit = Abc_MinInt( 2048, 20000000 / Gia_ManObjNum(pGia) );
    Limit = Abc_MinInt( Limit, 16000000 / Regs - 1 );
    if ( Limit < 2 ) return 1;
    pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pGia) );
    pStates = ABC_ALLOC( unsigned char, (Limit + 1) * Regs );
    pNext = ABC_ALLOC( unsigned char, Regs );
    pHeads = ABC_ALLOC( int, Bins ); pLinks = ABC_ALLOC( int, Limit + 1 );
    for ( i = 0; i < Bins; i++ ) pHeads[i] = -1;
    Gia_ManForEachPi( pGia, pObj, i ) pValues[Gia_ObjId(pGia, pObj)] = 2;
    for ( f = 0; f <= Limit; f++ )
    {
        if ( Cec_SuperStop(pWorker) ) break;
        Hash = 2166136261u;
        Gia_ManForEachRo( pGia, pObj, i )
        {
            unsigned char Value = pValues[Gia_ObjId(pGia, pObj)];
            pStates[f * Regs + i] = Value;
            Hash = (Hash ^ Value) * 16777619u;
        }
        Hash %= Bins;
        for ( k = pHeads[Hash]; k >= 0; k = pLinks[k] )
            if ( !memcmp(pStates + k * Regs, pStates + f * Regs, Regs) ) break;
        if ( k >= 0 ) { Prefix = f - k; break; }
        pLinks[f] = pHeads[Hash]; pHeads[Hash] = f;
        if ( f == Limit ) { Prefix = 1; break; }
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto cleanup;
            a = pValues[Gia_ObjFaninId0p(pGia, pObj)];
            b = pValues[Gia_ObjFaninId1p(pGia, pObj)];
            if ( a != 2 ) a ^= Gia_ObjFaninC0(pObj);
            if ( b != 2 ) b ^= Gia_ObjFaninC1(pObj);
            pValues[i] = !a || !b ? 0 : a == 1 && b == 1 ? 1 : 2;
        }
        Gia_ManForEachRi( pGia, pObj, i )
        {
            a = pValues[Gia_ObjFaninId0p(pGia, pObj)];
            pNext[i] = a == 2 ? 2 : a ^ Gia_ObjFaninC0(pObj);
        }
        Gia_ManForEachRo( pGia, pObj, i ) pValues[Gia_ObjId(pGia, pObj)] = pNext[i];
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: clock period=%d scanned=%d\n", Prefix, f );
cleanup:
    ABC_FREE(pValues); ABC_FREE(pStates); ABC_FREE(pNext); ABC_FREE(pHeads); ABC_FREE(pLinks);
    if ( Prefix > 1 && Prefix <= 32 && (ABC_INT64_T)Gia_ManObjNum(pGia) * Prefix <= 500000 )
        return Prefix;
    if ( Prefix > 1 )
        for ( i = 2; i <= 64 && i <= Prefix; i++ )
            if ( Prefix % i == 0 ) return i;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Combines transitions while retaining every intermediate output.]

  Description [The primary input sequence is in chronological order.]

  SideEffects [Uses the private input's Value fields.]

  SeeAlso     [Cec_SuperPhaseCex]

***********************************************************************/
static Gia_Man_t * Cec_SuperPhaseModel( Gia_Man_t * pGia, int Factor, Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pNew = NULL, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPis = NULL, * vState = NULL, * vNext = NULL, * vOuts = NULL;
    int i, f;
    if ( Factor < 2 || Factor > 64 || !Gia_ManRegNum(pGia) ||
         (ABC_INT64_T)Gia_ManObjNum(pGia) * Factor > 2000000 || Cec_SuperStop(pWorker) ) return NULL;
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    pNew->pName = Abc_UtilStrsav( pGia->pName );
    vPis = Vec_IntAlloc( Gia_ManPiNum(pGia) * Factor );
    vState = Vec_IntAlloc( Gia_ManRegNum(pGia) );
    vNext = Vec_IntStart( Gia_ManRegNum(pGia) );
    vOuts = Vec_IntAlloc( Gia_ManPoNum(pGia) * Factor );
    for ( i = 0; i < Gia_ManPiNum(pGia) * Factor; i++ )
    {
        if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto interrupted;
        Vec_IntPush( vPis, Gia_ManAppendCi(pNew) );
    }
    for ( i = 0; i < Gia_ManRegNum(pGia); i++ )
        Vec_IntPush( vState, Gia_ManAppendCi(pNew) );
    Gia_ManHashStart( pNew );
    for ( f = 0; f < Factor; f++ )
    {
        if ( Cec_SuperStop(pWorker) ) goto interrupted;
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachPi( pGia, pObj, i ) pObj->Value = Vec_IntEntry(vPis, f * Gia_ManPiNum(pGia) + i);
        Gia_ManForEachRo( pGia, pObj, i ) pObj->Value = Vec_IntEntry(vState, i);
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto interrupted;
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        Gia_ManForEachPo( pGia, pObj, i ) Vec_IntPush( vOuts, Gia_ObjFanin0Copy(pObj) );
        Gia_ManForEachRi( pGia, pObj, i ) Vec_IntWriteEntry( vNext, i, Gia_ObjFanin0Copy(pObj) );
        ABC_SWAP( Vec_Int_t *, vState, vNext );
    }
    Vec_IntForEachEntry( vOuts, f, i ) Gia_ManAppendCo( pNew, f );
    Vec_IntForEachEntry( vState, f, i ) Gia_ManAppendCo( pNew, f );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) );
    Gia_ManHashStop( pNew );
    if ( Cec_SuperStop(pWorker) ) goto interrupted;
    pNew = Gia_ManCleanup( pTemp = pNew ); Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 1 ); Gia_ManStop( pTemp );
    if ( Cec_SuperStop(pWorker) ) goto interrupted;
    goto cleanup;
interrupted:
    Gia_ManStopP( &pNew );
cleanup:
    Vec_IntFreeP( &vPis ); Vec_IntFreeP( &vState ); Vec_IntFreeP( &vNext ); Vec_IntFreeP( &vOuts );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Restores the input sequence from combined transitions.]

  Description [The portfolio still checks the trace on its original input.]

  SideEffects []

  SeeAlso     [Cec_SuperPhaseModel]

***********************************************************************/
static Abc_Cex_t * Cec_SuperPhaseCex( Gia_Man_t * pGia, Abc_Cex_t * pSource, int Factor )
{
    Abc_Cex_t * pCex;
    ABC_INT64_T Frame, Bits, SourceBits;
    int i, Pi = Gia_ManPiNum(pGia), Po = Gia_ManPoNum(pGia);
    if ( !pSource || Factor < 1 || Factor > 64 || !Po || pSource->nRegs < 0 ||
         pSource->iFrame < 0 || pSource->nPis != (ABC_INT64_T)Pi * Factor ||
         pSource->iPo < 0 || pSource->iPo >= (ABC_INT64_T)Po * Factor ) return NULL;
    Frame = (ABC_INT64_T)pSource->iFrame * Factor + pSource->iPo / Po;
    Bits = (Frame + 1) * Pi + Gia_ManRegNum(pGia);
    SourceBits = ((ABC_INT64_T)pSource->iFrame + 1) * pSource->nPis + pSource->nRegs;
    if ( Frame >= INT_MAX || Bits > INT_MAX - 32 || SourceBits > pSource->nBits ) return NULL;
    pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), Pi, (int)Frame + 1 );
    pCex->iFrame = (int)Frame;
    pCex->iPo = pSource->iPo % Po;
    for ( i = 0; i < (Frame + 1) * Pi; i++ )
        if ( Abc_InfoHasBit(pSource->pData, pSource->nRegs + i) )
            Abc_InfoSetBit( pCex->pData, pCex->nRegs + i );
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Simplifies a private model without changing its input order.]

  Description [Small inputs retain a sweep-before-rewrite recipe complementary
  to the shared startup graph. Larger inputs reuse completed preparation.]

  SideEffects []

  SeeAlso     [Cec_SuperPhaseSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperPhaseQuick( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker )
{
    if ( pGia == pWorker->pGia && Gia_ManRegNum(pGia) <= 512 && Gia_ManAndNum(pGia) < 10000 )
        pWorker->fInitial = 0;
    return Cec_SuperPrepare( pGia, pWorker, 0, 2, 0 );
}

/**Function*************************************************************

  Synopsis    [Keeps only correspondence that completes inside its slice.]

  Description []

  SideEffects [Temporarily shortens the worker deadline.]

  SeeAlso     [Cec_SuperPhaseSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperPhaseCorr( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker, int Seconds )
{
    Ssw_Pars_t Pars;
    Aig_Man_t * pAig, * pReduced;
    Gia_Man_t * pNew = NULL, * pTemp;
    abctime Deadline = pWorker->Deadline, Now = Abc_Clock();
    if ( Cec_SuperStop(pWorker) || !Gia_ManRegNum(pGia) || !Gia_ManPiNum(pGia) ) return NULL;
    if ( Deadline - Now > (abctime)Seconds * CLOCKS_PER_SEC )
        pWorker->Deadline = Now + (abctime)Seconds * CLOCKS_PER_SEC;
    Ssw_ManSetDefaultParams( &Pars );
    Pars.nBTLimit = 1000;
    Pars.fStopWhenGone = 0;
    Pars.pFunc = (void *)Cec_SuperStop;
    Pars.pData = pWorker;
    pAig = Gia_ManToAigSimple( pGia );
    pReduced = Ssw_SignalCorrespondence( pAig, &Pars );
    if ( pReduced && !pWorker->fInterrupted )
    {
        pNew = Gia_ManFromAigSimple( pReduced );
        pNew = Gia_ManDupNormalize( pTemp = pNew, 1 ); Gia_ManStop( pTemp );
    }
    if ( pReduced ) Aig_ManStop( pReduced );
    Aig_ManStop( pAig );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Complements the unmodified searches with clock-period folding.]

  Description [Period detection is a heuristic; all folded outputs remain
  proof obligations. No transformed graph is shared with other workers.]

  SideEffects [May attach a restored counterexample to the worker input.]

  SeeAlso     [Cec_SuperPhasePeriod Cec_SuperPhaseModel Cec_SuperPhaseCex]

***********************************************************************/
static int Cec_SuperPhaseSolve( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia, * pModel = NULL, * pNext;
    Aig_Man_t * pAig = NULL;
    Pdr2_Par_t Pars;
    Abc_Cex_t * pCex;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock(), Now;
    int Factor, Result = -1;
    if ( Gia_ManObjNum(pGia) > 250000 || Gia_ManRegNum(pGia) > 10000 ) return -1;
    if ( Deadline - Start > CLOCKS_PER_SEC / 4 ) pWorker->Deadline = Start + CLOCKS_PER_SEC / 4;
    Factor = Cec_SuperPhasePeriod( pGia, pWorker );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    if ( Cec_SuperStop(pWorker) ) return -1;
    // A small model can expose a hidden period after correspondence.
    if ( Factor < 2 && (Gia_ManRegNum(pGia) > 512 || Gia_ManAndNum(pGia) >= 10000) ) return -1;
    pModel = Cec_SuperPhaseQuick( pGia, pWorker );
    pNext = Cec_SuperPhaseCorr( pModel, pWorker, 2 );
    if ( pNext ) { Gia_ManStop(pModel); pModel = pNext; }
    Result = Cec_SuperConstant(pModel) == 1 ? 1 : -1;
    if ( Result == 1 || Cec_SuperStop(pWorker) ) goto cleanup;
    Result = -1;
    Now = Abc_Clock();
    if ( Deadline - Now > CLOCKS_PER_SEC / 4 ) pWorker->Deadline = Now + CLOCKS_PER_SEC / 4;
    Factor = Cec_SuperPhasePeriod( pModel, pWorker );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    if ( Factor < 2 || Cec_SuperStop(pWorker) ) goto cleanup;
    if ( !pWorker->pMan->pPars->iEngine && pWorker->pMan->nWorkers >= 4 )
    {
        Deadline = pWorker->Deadline = pWorker->pMan->Deadline;
        pWorker->Seconds = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: phase period=%d continuing within the command deadline\n", Factor );
    }
    pNext = Cec_SuperPhaseModel( pModel, Factor, pWorker );
    if ( !pNext ) goto cleanup;
    Gia_ManStop(pModel); pModel = pNext;
    pNext = Cec_SuperPhaseQuick( pModel, pWorker ); Gia_ManStop(pModel); pModel = pNext;
    pNext = Cec_SuperPhaseCorr( pModel, pWorker, 3 );
    if ( pNext ) { Gia_ManStop(pModel); pModel = pNext; }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: clock folding factor=%d pi=%d ff=%d and=%d elapsed=%.3f sec\n",
            Factor, Gia_ManPiNum(pModel), Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    Result = Cec_SuperConstant(pModel) == 1 ? 1 : -1;
    if ( Result == 1 || Cec_SuperStop(pWorker) ) goto cleanup;
    Result = -1;
    if ( !Gia_ManRegNum(pModel) )
    {
        Bmc_GiaPar_t Bmc;
        Bmc_GiaSetDefaultParams( &Bmc );
        Bmc.nFramesMax = 1;
        Bmc.nMemoryLimit = pWorker->pMan->pPars->nBmcMemory;
        Bmc.TimeToStop = pWorker->Deadline;
        Bmc.pFuncStop = Cec_SuperStop;
        Bmc.pStopData = pWorker;
        Bmc.fSilent = 1;
        Result = Bmc_GiaPerform( pModel, &Bmc );
    }
    else
    {
        Pdr2_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = Abc_MaxInt(1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC));
        Pars.pFuncStop = Cec_SuperStopId;
        Pars.fSilent = 1;
        Pars.nAbsRuns = Pars.nBmcTime = 0;
        Pars.fVerifyComplete = 1;
        pAig = Gia_ManToAigSimple( pModel );
        Result = Pdr2_ManSolve( pAig, &Pars );
    }
    if ( Result == 0 )
    {
        pCex = Cec_SuperPhaseCex( pGia, pAig ? pAig->pSeqModel : pModel->pCexSeq, Factor );
        if ( pCex )
        {
            Abc_CexFreeP( &pGia->pCexSeq );
            pGia->pCexSeq = pCex;
        }
        else
        {
            Abc_Print( 1, "Warning: super_prove rejected a malformed clock-folded counterexample.\n" );
            Result = -1;
        }
    }
cleanup:
    pWorker->Deadline = Deadline;
    if ( pAig ) Aig_ManStop(pAig);
    Gia_ManStopP(&pModel);
    return Result;
}


/**Function*************************************************************

  Synopsis    [Selects the last Boolean-register transient in a ternary prefix.]

  Description [The all-output safe prefix is established independently. Selection
  only changes the search model, never the proof obligation.]

  SideEffects []

  SeeAlso     [Cec_SuperStartupSolve]

***********************************************************************/
static int Cec_SuperStartupPrefix( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker,
    int * pSafe, int fSelectTransient )
{
    const int Bins = 4093;
    unsigned char * pValues, * pStates, * pNext;
    int * pHeads, * pLinks;
    Gia_Obj_t * pObj;
    int i, f, k, a, b, Regs = Gia_ManRegNum(pGia), Limit, Prefix = 1, fSafe = 1;
    unsigned Hash;
    *pSafe = 0;
    if ( !Regs ) return 0;
    Limit = Abc_MinInt( 2048, 20000000 / Gia_ManObjNum(pGia) );
    Limit = Abc_MinInt( Limit, 16000000 / Regs - 1 );
    if ( Limit < 2 ) return 1;
    pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pGia) );
    pStates = ABC_ALLOC( unsigned char, (Limit + 1) * Regs );
    pNext = ABC_ALLOC( unsigned char, Regs );
    pHeads = ABC_ALLOC( int, Bins ); pLinks = ABC_ALLOC( int, Limit + 1 );
    for ( i = 0; i < Bins; i++ ) pHeads[i] = -1;
    Gia_ManForEachPi( pGia, pObj, i ) pValues[Gia_ObjId(pGia, pObj)] = 2;
    for ( f = 0; f <= Limit; f++ )
    {
        if ( Cec_SuperStop(pWorker) ) break;
        Hash = 2166136261u;
        Gia_ManForEachRo( pGia, pObj, i )
        {
            unsigned char Value = pValues[Gia_ObjId(pGia, pObj)];
            pStates[f * Regs + i] = Value;
            Hash = (Hash ^ Value) * 16777619u;
        }
        Hash %= Bins;
        for ( k = pHeads[Hash]; k >= 0; k = pLinks[k] )
            if ( !memcmp(pStates + k * Regs, pStates + f * Regs, Regs) ) break;
        if ( k >= 0 ) { Prefix = Abc_MaxInt( 1, k ); break; }
        pLinks[f] = pHeads[Hash]; pHeads[Hash] = f;
        if ( f == Limit ) { Prefix = Limit; break; }
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( !(i & 1023) && Cec_SuperStop(pWorker) ) goto cleanup;
            a = pValues[Gia_ObjFaninId0p(pGia, pObj)];
            b = pValues[Gia_ObjFaninId1p(pGia, pObj)];
            if ( a != 2 ) a ^= Gia_ObjFaninC0(pObj);
            if ( b != 2 ) b ^= Gia_ObjFaninC1(pObj);
            pValues[i] = !a || !b ? 0 : a == 1 && b == 1 ? 1 : 2;
        }
        Gia_ManForEachPo( pGia, pObj, i )
        {
            a = pValues[Gia_ObjFaninId0p(pGia, pObj)];
            if ( a != 2 ) a ^= Gia_ObjFaninC0(pObj);
            if ( a ) fSafe = 0;
        }
        if ( fSafe ) *pSafe = f + 1;
        Gia_ManForEachRi( pGia, pObj, i )
        {
            a = pValues[Gia_ObjFaninId0p(pGia, pObj)];
            pNext[i] = a == 2 ? 2 : a ^ Gia_ObjFaninC0(pObj);
        }
        Gia_ManForEachRo( pGia, pObj, i ) pValues[Gia_ObjId(pGia, pObj)] = pNext[i];
    }
    if ( fSelectTransient && Prefix > 1 && !Cec_SuperStop(pWorker) )
    {
        int r, j, Last, Best = 0;
        // A register that settles to a Boolean constant marks a useful end
        // of startup. Later data-dependent states can make the unroll larger.
        for ( r = 0; r < Regs; r++ )
        {
            if ( pStates[f * Regs + r] == 2 ) continue;
            Last = 0;
            for ( j = 1; j <= f; j++ )
                if ( pStates[j * Regs + r] != pStates[(j - 1) * Regs + r] ) Last = j;
            if ( Last > Best && Last < Prefix && Last < *pSafe ) Best = Last;
        }
        if ( Best )
        {
            if ( pWorker->pMan->pPars->fVerbose )
                Abc_Print( 1, "super_prove: startup transient=%d selected=%d\n", Prefix, Best );
            Prefix = Best;
        }
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: startup prefix=%d safe=%d scanned=%d\n", Prefix, *pSafe, f );
cleanup:
    ABC_FREE(pValues); ABC_FREE(pStates); ABC_FREE(pNext); ABC_FREE(pHeads); ABC_FREE(pLinks);
    return Prefix;
}

/**Function*************************************************************

  Synopsis    [Computes completed correspondence at a requested induction depth.]

  Description [An interrupted reduction is discarded. Input and output orders stay
  unchanged so a later trace can be reconstructed.]

  SideEffects [Uses the worker deadline.]

  SeeAlso     [Cec_SuperStartupSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperStartupCorr( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker, int Seconds, int Depth )
{
    Ssw_Pars_t Pars;
    Aig_Man_t * pAig, * pReduced;
    Gia_Man_t * pNew = NULL, * pTemp;
    abctime Deadline = pWorker->Deadline, Now = Abc_Clock();
    if ( Cec_SuperStop(pWorker) || !Gia_ManRegNum(pGia) || !Gia_ManPiNum(pGia) ) return NULL;
    if ( Deadline - Now > (abctime)Seconds * CLOCKS_PER_SEC )
        pWorker->Deadline = Now + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( pWorker->Engine == SUPER_BDD_SIMPLIFY )
    {
        Cec_ParCor_t Cor;
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nProcs = 1;
        Cor.nBTLimit = 1000;
        Cor.nFrames = Depth;
        Cor.pFunc = (void *)Cec_SuperStop;
        Cor.pData = pWorker;
        pTemp = Gia_ManDupNormalize( pGia, 1 );
        pNew = Cec_ManLSCorrespondence4( pTemp, &Cor, 4, 0 );
        Gia_ManStop( pTemp );
        if ( pWorker->fInterrupted ) Gia_ManStopP( &pNew );
        if ( pNew )
        {
            pNew = Gia_ManDupNormalize( pTemp = pNew, 1 );
            Gia_ManStop( pTemp );
        }
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: deep scorr4 depth=%d stopped=%d ff=%d -> %d elapsed=%.6f sec\n",
                Depth, pWorker->fInterrupted, Gia_ManRegNum(pGia),
                pNew ? Gia_ManRegNum(pNew) : Gia_ManRegNum(pGia),
                (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        return pNew;
    }
    Ssw_ManSetDefaultParams( &Pars );
    Pars.nBTLimit = 1000;
    Pars.nFramesK = Depth;
    Pars.fStopWhenGone = 0;
    Pars.pFunc = (void *)Cec_SuperStop;
    Pars.pData = pWorker;
    pAig = Gia_ManToAigSimple( pGia );
    pReduced = Ssw_SignalCorrespondence( pAig, &Pars );
    if ( pReduced && !pWorker->fInterrupted )
    {
        pNew = Gia_ManFromAigSimple( pReduced );
        pNew = Gia_ManDupNormalize( pTemp = pNew, 1 ); Gia_ManStop( pTemp );
    }
    if ( pReduced ) Aig_ManStop( pReduced );
    Aig_ManStop( pAig );
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: deep correspondence depth=%d stopped=%d ff=%d -> %d elapsed=%.6f sec\n",
            Depth, pWorker->fInterrupted, Gia_ManRegNum(pGia), pNew ? Gia_ManRegNum(pNew) : Gia_ManRegNum(pGia),
            (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    return pNew;
}
/**Function*************************************************************

  Synopsis    [Simplifies a private model between completed correspondence steps.]

  Description [Each completed graph preserves the sequential behavior and
  interface. An interrupted step leaves the last completed graph available.]

  SideEffects [Temporarily narrows the worker deadline.]

  SeeAlso     [Cec_SuperBddSolve]

***********************************************************************/
static Gia_Man_t * Cec_SuperDeepSimplify( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker )
{
    abctime Start = Abc_Clock();
    Gia_Man_t * pNew = Cec_SuperPrepare( pGia, pWorker, 1, 2, 0 );
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: deep synthesis ff=%d -> %d and=%d -> %d elapsed=%.6f sec\n",
            Gia_ManRegNum(pGia), Gia_ManRegNum(pNew), Gia_ManAndNum(pGia), Gia_ManAndNum(pNew),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Combines deeper correspondence with bounded reachability and PDR2.]

  Description [Completed reductions expose a smaller sequential model. A
  separately certified prefix permits temporal simplification. BDD proof
  search receives two seconds, then PDR2 uses the same reparameterized model.]

  SideEffects [May attach an original-input trace to the worker graph.]

  SeeAlso     [Cec_SuperStartupCorr Cec_SuperStartupPrefix Cec_SuperRpm]

***********************************************************************/
static int Cec_SuperBddSolve( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia, * pBase = NULL, * pModel = NULL, * pNext;
    Abc_Cex_t * pCex;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Depth, Prefix = 0, Safe = 0, Result = -1;
    if ( Gia_ManObjNum(pGia) > 100000 )
        return -1;
    pBase = Cec_SuperDeepSimplify( pGia, pWorker );
    for ( Depth = 1; Depth <= 4 && !Cec_SuperStop(pWorker); Depth *= 4 )
    {
        pNext = Cec_SuperStartupCorr( pBase, pWorker, 2, Depth );
        if ( pNext ) { Gia_ManStop(pBase); pBase = pNext; }
        pNext = Cec_SuperDeepSimplify( pBase, pWorker );
        Gia_ManStop( pBase );
        pBase = pNext;
    }
    if ( Cec_SuperConstant(pBase) == 1 ) { Result = 1; goto cleanup; }
    if ( Cec_SuperStop(pWorker) ) goto cleanup;
    if ( Gia_ManRegNum(pBase) )
    {
        Prefix = Cec_SuperStartupPrefix( pBase, pWorker, &Safe, 1 );
        Prefix = Abc_MinInt( Prefix, Abc_MaxInt(0, Safe - 1) );
    }
    Cec_SuperSetGia( pWorker, pBase );
    pModel = Prefix ? Cec_SuperTemporalModel(pWorker, Prefix) : Gia_ManDup(pBase);
    Cec_SuperSetGia( pWorker, pGia );
    if ( !pModel || Cec_SuperStop(pWorker) ) goto cleanup;
    for ( Depth = 1; Prefix && Depth <= 2 && !Cec_SuperStop(pWorker); Depth++ )
    {
        pNext = Cec_SuperDeepSimplify( pModel, pWorker );
        Gia_ManStop( pModel );
        pModel = pNext;
        pNext = Cec_SuperStartupCorr( pModel, pWorker, 2, Depth );
        if ( pNext ) { Gia_ManStop(pModel); pModel = pNext; }
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: deep model prefix=%d pi=%d ff=%d and=%d elapsed=%.3f sec\n",
            Prefix, Gia_ManPiNum(pModel), Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( Cec_SuperConstant(pModel) == 1 ) { Result = 1; goto cleanup; }
    if ( Cec_SuperStop(pWorker) ) goto cleanup;
    Cec_SuperSetGia( pWorker, pModel );
    Result = Cec_SuperRpm( pWorker, 0, 100000, 1 );
    Cec_SuperSetGia( pWorker, pGia );
    if ( Result == 0 )
    {
        if ( Prefix ) pCex = Cec_SuperTemporalCex(pGia, pModel->pCexSeq, Prefix);
        else
        {
            pCex = pModel->pCexSeq;
            pModel->pCexSeq = NULL;
        }
        if ( pCex ) { Abc_CexFreeP(&pGia->pCexSeq); pGia->pCexSeq = pCex; }
        else
        {
            Abc_Print( 1, "Warning: super_prove rejected a malformed deep-preprocessing counterexample.\n" );
            Result = -1;
        }
    }
cleanup:
    pWorker->Deadline = Deadline;
    Cec_SuperSetGia( pWorker, pGia );
    Gia_ManStopP( &pBase );
    Gia_ManStopP( &pModel );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Solves after a certified long startup and input reparameterization.]

  Description [A short raw-model probe detects a long repeated-state prefix.
  Completed correspondence exposes a useful transient, whose exact reachable
  states become the initial relation. All skipped outputs are certified zero.
  Abstract PDR2 then searches the private reparameterized model.]

  SideEffects [May attach an original-order trace to the private input graph.]

  SeeAlso     [Cec_SuperStartupPrefix Cec_SuperRpm Cec_SuperTemporalCex]

***********************************************************************/
static int Cec_SuperStartupSolve( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia, * pBase = NULL, * pModel = NULL, * pNext;
    Abc_Cex_t * pTrace;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Prefix, Safe = 0, Depth, Result = -1;
    if ( Gia_ManRegNum(pGia) > 512 || Gia_ManObjNum(pGia) > 30000 ) return -1;
    if ( Deadline - Start > CLOCKS_PER_SEC / 4 ) pWorker->Deadline = Start + CLOCKS_PER_SEC / 4;
    Prefix = Cec_SuperStartupPrefix( pGia, pWorker, &Safe, 0 );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    Prefix = Abc_MinInt( Prefix, Abc_MaxInt(0, Safe - 1) );
    if ( Prefix <= 16 || Cec_SuperStop(pWorker) ) return -1;
    pBase = Cec_SuperPhaseQuick( pGia, pWorker );
    for ( Depth = 1; Depth <= 2 && !Cec_SuperStop(pWorker); Depth++ )
    {
        pNext = Cec_SuperStartupCorr( pBase, pWorker, 2, Depth );
        if ( pNext ) { Gia_ManStop(pBase); pBase = pNext; }
        pNext = Cec_SuperPhaseQuick( pBase, pWorker ); Gia_ManStop(pBase); pBase = pNext;
    }
    if ( Cec_SuperConstant(pBase) == 1 ) { Result = 1; goto cleanup; }
    if ( Cec_SuperStop(pWorker) ) goto cleanup;
    Prefix = Cec_SuperStartupPrefix( pBase, pWorker, &Safe, 1 );
    Prefix = Abc_MinInt( Prefix, Abc_MaxInt(0, Safe - 1) );
    if ( Prefix <= 16 || Cec_SuperStop(pWorker) ) goto cleanup;
    Cec_SuperSetGia( pWorker, pBase );
    pModel = Cec_SuperTemporalModel( pWorker, Prefix );
    Cec_SuperSetGia( pWorker, pGia );
    if ( !pModel || Cec_SuperStop(pWorker) ) goto cleanup;
    for ( Depth = 1; Depth <= 2 && !Cec_SuperStop(pWorker); Depth++ )
    {
        pNext = Cec_SuperPhaseQuick( pModel, pWorker ); Gia_ManStop(pModel); pModel = pNext;
        pNext = Cec_SuperStartupCorr( pModel, pWorker, 2, Depth );
        if ( pNext ) { Gia_ManStop(pModel); pModel = pNext; }
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: startup model prefix=%d pi=%d ff=%d and=%d elapsed=%.3f sec\n",
            Prefix, Gia_ManPiNum(pModel), Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( Cec_SuperConstant(pModel) == 1 ) { Result = 1; goto cleanup; }
    if ( Cec_SuperStop(pWorker) ) goto cleanup;
    Cec_SuperSetGia( pWorker, pModel );
    Result = Cec_SuperRpm( pWorker, 1, 2000000, 0 );
    Cec_SuperSetGia( pWorker, pGia );
    if ( Result == 0 )
    {
        pTrace = Cec_SuperTemporalCex( pGia, pModel->pCexSeq, Prefix );
        if ( pTrace ) { Abc_CexFreeP(&pGia->pCexSeq); pGia->pCexSeq = pTrace; }
        else
        {
            Abc_Print( 1, "Warning: super_prove rejected a malformed startup counterexample.\n" );
            Result = -1;
        }
    }
cleanup:
    pWorker->Deadline = Deadline;
    Cec_SuperSetGia( pWorker, pGia );
    Gia_ManStopP( &pBase );
    Gia_ManStopP( &pModel );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs gate abstraction on a private temporal model.]

  Description [Uses the synchronous proof hook on this worker. Abstract
  counterexamples stay inside refinement and cannot become portfolio answers.]

  SideEffects [May attach a concrete counterexample to the private model.]

  SeeAlso     [Cec_SuperGlaProve Cec_SuperTemporalSolve]

***********************************************************************/
static int Cec_SuperTemporalGla( Gia_Man_t * pGia, Cec_SuperWorker_t * pWorker )
{
    Abs_Par_t Pars;
    if ( Gia_ManPoNum(pGia) != 1 || !Gia_ManPiNum(pGia) ) return -1;
    Abs_ParSetDefaults( &Pars );
    Pars.fSilent = !pWorker->pMan->pPars->fVerbose;
    Pars.nTimeOut = Abc_MaxInt( 1,
        (int)((pWorker->Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
    Pars.nFramesMax = 1000;
    Pars.fCallProver = 0;
    Pars.pFuncStop = Cec_SuperStopId;
    Pars.pFuncProve = Cec_SuperGlaProve;
    Pars.pProveData = pWorker;
    return Gia_ManPerformGla( pGia, &Pars );
}

/**Function*************************************************************

  Synopsis    [Proves an initial prefix and solves from its reachable states.]

  Description [This complementary model stays private. A proof requires both
  the prefix and the transformed remainder to be safe. SAT candidates regain
  the removed inputs before the ordinary original-graph replay.]

  SideEffects [May attach an original-order trace to the worker's graph.]

  SeeAlso     [Cec_SuperTemporalModel Cec_SuperTemporalCex]

***********************************************************************/
static int Cec_SuperTemporalSolve( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia, * pModel = NULL, * pNext;
    Aig_Man_t * pAig = NULL;
    Abc_Cex_t * pSource;
    Bmc_GiaPar_t Bmc;
    Pdr2_Par_t Pars;
    abctime Start = Abc_Clock();
    int i, Result, Prefix = 1;
    Bmc_GiaSetDefaultParams( &Bmc );
    Bmc.nFramesMax = Prefix;
    Bmc.nMemoryLimit = 512;
    Bmc.nTimeOut = 2;
    Bmc.TimeToStop = pWorker->Deadline;
    Bmc.pFuncStop = Cec_SuperStop;
    Bmc.pStopData = pWorker;
    Bmc.fSilent = 1;
    Result = Bmc_GiaPerform( pGia, &Bmc );
    if ( Result >= 0 || Bmc.nFramesDone < Prefix || Cec_SuperStop(pWorker) ) return Result;
    pModel = Cec_SuperTemporalModel( pWorker, Prefix );
    if ( !pModel ) return -1;
    for ( i = 0; i < 3 && !Cec_SuperStop(pWorker); i++ )
    {
        if ( i == 1 && !pWorker->pMan->pPars->fRewrite ) continue;
        pNext = i == 1 ? Drw_ManRwsatWithStop(pModel, 0, 0, Cec_SuperStop, pWorker) :
            Gia_ManSeqStructSweepWithStop(pModel, 1, 1, 0, Cec_SuperStop, pWorker);
        if ( !pNext ) break;
        Gia_ManStop( pModel ); pModel = pNext;
    }
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: temporal prefix=%d pi=%d ff=%d and=%d elapsed=%.3f sec\n",
            Prefix, Gia_ManPiNum(pModel), Gia_ManRegNum(pModel), Gia_ManAndNum(pModel),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( Cec_SuperStop(pWorker) ) goto cleanup;
    if ( pWorker->Engine == SUPER_GLA_TEMPORAL )
    {
        Result = Cec_SuperTemporalGla( pModel, pWorker );
        pSource = pModel->pCexSeq;
    }
    else
    {
        Pdr2_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = Abc_MaxInt( 1,
            (int)((pWorker->Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
        Pars.pFuncStop = Cec_SuperStopId;
        Pars.fSilent = 1;
        Pars.nAbsRuns = 0;
        Pars.nBmcTime = 0;
        Pars.fVerifyComplete = 1;
        pAig = Gia_ManToAigSimple( pModel );
        Result = Pdr2_ManSolve( pAig, &Pars );
        pSource = pAig->pSeqModel;
    }
    if ( Result == 0 )
    {
        Abc_CexFreeP( &pGia->pCexSeq );
        pGia->pCexSeq = Cec_SuperTemporalCex( pGia, pSource, Prefix );
        if ( !pGia->pCexSeq )
        {
            Abc_Print( 1, "Warning: super_prove rejected a malformed counterexample from %s.\n",
                Cec_ManSuperEngineName(pWorker->Engine) );
            Result = -1;
        }
    }
    if ( pAig ) Aig_ManStop( pAig );
cleanup:
    Gia_ManStop( pModel );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries a short CaDiCaL search before the scalable BMC search.]

  Description [Uses one worker throughout and retains the overall deadline.]

  SideEffects [May produce a concrete counterexample on the private model.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperBmcRace( Cec_SuperWorker_t * pWorker )
{
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Result, Engine = pWorker->Engine, Seconds = pWorker->Seconds;
    if ( Deadline - Start > 15 * (abctime)CLOCKS_PER_SEC )
        pWorker->Deadline = Start + 15 * (abctime)CLOCKS_PER_SEC;
    pWorker->Seconds = Abc_MinInt( Seconds, 15 );
    pWorker->Engine = SUPER_BMC3_CADICAL;
    Result = Cec_SuperSolve( pWorker );
    pWorker->Deadline = Deadline;
    pWorker->Seconds = Seconds;
    pWorker->fInterrupted = 0;
    if ( Result < 0 && !Cec_SuperStop(pWorker) )
    {
        pWorker->Engine = SUPER_BMC3_GLUCOSE;
        Result = Cec_SuperSolve( pWorker );
    }
    pWorker->Engine = Engine;
    Cec_SuperLaneWinner( pWorker, Engine, Result );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries interpolation on a privately synthesized model.]

  Description [The preprocessing slice is bounded. Input ordering remains
  unchanged, and the portfolio replays every trace on its original model.]

  SideEffects [May replace the worker's graph.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperIntSyn2( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pNew, * pTemp;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Result, Engine = pWorker->Engine, Seconds = pWorker->Seconds;
    pNew = Cec_SuperPrepare( pWorker->pGia, pWorker, 1, 3, 0 );
    Gia_ManStop( pWorker->pGia );
    Cec_SuperSetGia( pWorker, pNew );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: interpolation synthesis and=%d ff=%d elapsed=%.3f sec\n",
            Gia_ManAndNum(pWorker->pGia), Gia_ManRegNum(pWorker->pGia),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( Cec_SuperStop(pWorker) ) return -1;
    Cec_SuperSetGia( pWorker, Gia_ManDupNormalize(pTemp = pWorker->pGia, 1) );
    Gia_ManStop( pTemp );
    pWorker->Seconds = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
    pWorker->Engine = SUPER_INT_OLD;
    Result = Cec_SuperSolve( pWorker );
    pWorker->Engine = Engine;
    pWorker->Seconds = Seconds;
    Cec_SuperLaneWinner( pWorker, Engine, Result );
    return Result;
}


/**Function*************************************************************

  Synopsis    [Combines structural synthesis with inductive correspondence.]

  Description [Keeps this representation private and publishes only a
  completed correspondence reduction.]

  SideEffects [May replace the worker's graph.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperSyn2Corr( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pNew, * pNorm;
    Aig_Man_t * pAig, * pReduced;
    Ssw_Pars_t Pars;
    abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
    int Result = -1, Engine = pWorker->Engine;
    pNew = Cec_SuperPrepare( pWorker->pGia, pWorker, 1, 3, 1 );
    Gia_ManStop( pWorker->pGia );
    Cec_SuperSetGia( pWorker, pNew );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = 0;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: syn2 sweep and=%d ff=%d elapsed=%.3f sec\n",
            Gia_ManAndNum(pWorker->pGia), Gia_ManRegNum(pWorker->pGia),
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    Result = Cec_SuperConstant( pWorker->pGia );
    if ( Result >= 0 || Cec_SuperStop(pWorker) ) goto finish;
    if ( Engine == SUPER_RETIME_SCORR && Gia_ManRegNum(pWorker->pGia) )
    {
        abctime Now = Abc_Clock();
        if ( Deadline - Now > 3 * (abctime)CLOCKS_PER_SEC )
            pWorker->Deadline = Now + 3 * (abctime)CLOCKS_PER_SEC;
        pNew = Gia_ManRetimeForwardWithStop( pWorker->pGia, 20, 100000, Cec_SuperStop, pWorker );
        if ( pNew )
        {
            Gia_ManStop( pWorker->pGia );
            Cec_SuperSetGia( pWorker, pNew );
            // Retain constant registers as candidate invariants for induction.
            pNew = Gia_ManSeqStructSweepWithStop( pNew, 0, 1, 0, Cec_SuperStop, pWorker );
            if ( pNew )
            {
                Gia_ManStop( pWorker->pGia );
                Cec_SuperSetGia( pWorker, pNew );
            }
            pNew = Drw_ManRwsatWithStop( pWorker->pGia, 0, 0, Cec_SuperStop, pWorker );
            if ( pNew )
            {
                Gia_ManStop( pWorker->pGia );
                Cec_SuperSetGia( pWorker, pNew );
            }
        }
        else
        {
            pWorker->Deadline = Deadline;
            goto finish;
        }
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: retimed and=%d ff=%d elapsed=%.3f sec\n",
                Gia_ManAndNum(pWorker->pGia), Gia_ManRegNum(pWorker->pGia),
                (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC );
        Result = Cec_SuperConstant( pWorker->pGia );
        if ( Result >= 0 || Cec_SuperStop(pWorker) ) goto finish;
    }
    if ( Gia_ManRegNum(pWorker->pGia) && Gia_ManPiNum(pWorker->pGia) )
    {
        Ssw_ManSetDefaultParams( &Pars );
        if ( Engine == SUPER_RETIME_SCORR ) Pars.nFramesK = 4;
        Pars.pFunc = (void *)Cec_SuperStop;
        Pars.pData = pWorker;
        pAig = Gia_ManToAigSimple( pWorker->pGia );
        pReduced = Ssw_SignalCorrespondence( pAig, &Pars );
        if ( pReduced )
        {
            if ( !pWorker->fInterrupted )
            {
                pNew = Gia_ManFromAigSimple( pReduced );
                pNorm = Gia_ManDupNormalize( pNew, 1 );
                Gia_ManStop( pNew );
                Gia_ManStop( pWorker->pGia );
                Cec_SuperSetGia( pWorker, pNorm );
            }
            Aig_ManStop( pReduced );
        }
        Aig_ManStop( pAig );
        Result = Cec_SuperConstant( pWorker->pGia );
        if ( Result >= 0 || Cec_SuperStop(pWorker) ) goto finish;
        Cec_SuperReduce( pWorker, Gia_ManDup(pWorker->pGia) );
    }
    if ( !pWorker->pMan->pPars->iEngine ) goto finish;
    pWorker->Engine = SUPER_PDR2;
    Result = Cec_SuperSolve( pWorker );
finish:
    pWorker->Engine = Engine;
    Cec_SuperLaneWinner( pWorker, Engine, Result );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Advances a private generator matching narrow rarity simulation.]

  Description [The caller owns both words of generator state.]

  SideEffects [Updates the generator state.]

  SeeAlso     [Cec_SuperSimPattern]

***********************************************************************/
static unsigned Cec_SuperSimRandom( unsigned * pState )
{
    pState[0] = 36969u * (pState[0] & 65535u) + (pState[0] >> 16);
    pState[1] = 18000u * (pState[1] & 65535u) + (pState[1] >> 16);
    return (pState[0] << 16) + pState[1];
}

/**Function*************************************************************

  Synopsis    [Generates the random and fixed patterns for one primary input.]

  Description []

  SideEffects [Updates the caller's generator state.]

  SeeAlso     [Cec_SuperSimulateDirect]

***********************************************************************/
static word Cec_SuperSimPattern( unsigned * pState, int Input )
{
    word Value = Cec_SuperSimRandom( pState );
    Value |= (word)Cec_SuperSimRandom(pState) << 32;
    return (Value << 4) | ((Input & 1) ? 0xA : 0xC);
}

/**Function*************************************************************

  Synopsis    [Checks a rarity candidate while allowing a rejected phase to advance.]

  Description [Keeps the verified original trace for publication, avoiding
  another replay when the caller returns from a pipeline.]

  SideEffects [Consumes the candidate and updates the private graph.]

  SeeAlso     [Cec_SuperPublish]

***********************************************************************/
static int Cec_SuperRarityCandidate( Cec_SuperWorker_t * pWorker, Abc_Cex_t * pCex )
{
    if ( !pCex ) return 0;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: rarity candidate frame=%d; replaying on the original graph.\n", pCex->iFrame );
    assert( pWorker->pCheckedCex == NULL );
    Abc_CexFreeP( &pWorker->pGia->pCexSeq );
    pWorker->pGia->pCexSeq = pCex;
    pWorker->pCheckedCex = Cec_SuperCheckCex( pWorker );
    if ( pWorker->pCheckedCex ) return 1;
    Abc_CexFreeP( &pWorker->pGia->pCexSeq );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Simulates narrow trajectories directly on the worker's GIA.]

  Description [Preserves the first one-word rarity trajectory from reset.
  This probe performs no state selection and never returns a safety proof.
  A hit is regenerated from its seed and checked on the original graph,
  even after the deadline. Publication reuses that verified trace.]

  SideEffects [Replaces the worker's counterexample on a verified hit.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperSimulateDirect( Cec_SuperWorker_t * pWorker, int nFrames )
{
    Gia_Man_t * pGia = pWorker->pGia;
    Gia_Obj_t * pObj, * pRi;
    unsigned State[2] = { 3716960521u, 2174103536u };
    word * pSim = ABC_CALLOC( word, Gia_ManObjNum(pGia) );
    int i, Frame = 0, Pattern = -1, Output = -1, Result = -1;
    Cec_SuperSimRandom( State );
    for ( Frame = 0; Frame < nFrames; Frame++ )
    {
        if ( Cec_SuperStop(pWorker) ) break;
        Gia_ManForEachPi( pGia, pObj, i )
        {
            if ( !(i & 4095) && Cec_SuperStop(pWorker) ) goto finish;
            pSim[Gia_ObjId(pGia, pObj)] = Cec_SuperSimPattern( State, i );
        }
        if ( Frame )
            Gia_ManForEachRiRo( pGia, pRi, pObj, i )
                pSim[Gia_ObjId(pGia, pObj)] = pSim[Gia_ObjId(pGia, pRi)];
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( !(i & 4095) && Cec_SuperStop(pWorker) ) goto finish;
            pSim[i] = (pSim[Gia_ObjFaninId0(pObj, i)] ^ -(word)Gia_ObjFaninC0(pObj)) &
                      (pSim[Gia_ObjFaninId1(pObj, i)] ^ -(word)Gia_ObjFaninC1(pObj));
        }
        Gia_ManForEachCo( pGia, pObj, i )
        {
            if ( !(i & 4095) && Cec_SuperStop(pWorker) ) goto finish;
            pSim[Gia_ObjId(pGia, pObj)] = pSim[Gia_ObjFaninId0p(pGia, pObj)] ^ -(word)Gia_ObjFaninC0(pObj);
        }
        Gia_ManForEachPo( pGia, pObj, i )
            if ( pSim[Gia_ObjId(pGia, pObj)] )
            {
                for ( Pattern = 0; !((pSim[Gia_ObjId(pGia, pObj)] >> Pattern) & 1); Pattern++ ) {}
                Output = i;
                break;
            }
        if ( Pattern >= 0 ) break;
    }
    if ( Pattern >= 0 && (ABC_INT64_T)Gia_ManPiNum(pGia) * (Frame + 1) + Gia_ManRegNum(pGia) <= INT_MAX )
    {
        Abc_Cex_t * pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), Gia_ManPiNum(pGia), Frame + 1 );
        int f, Bit = Gia_ManRegNum(pGia);
        pCex->iFrame = Frame;
        pCex->iPo = Output;
        State[0] = 3716960521u;
        State[1] = 2174103536u;
        Cec_SuperSimRandom( State );
        for ( f = 0; f <= Frame; f++ )
            for ( i = 0; i < Gia_ManPiNum(pGia); i++, Bit++ )
                if ( (Cec_SuperSimPattern(State, i) >> Pattern) & 1 ) Abc_InfoSetBit( pCex->pData, Bit );
        assert( Bit == pCex->nBits );
        if ( Cec_SuperRarityCandidate(pWorker, pCex) ) Result = 0;
    }
finish:
    pWorker->nDirectFrames = Frame;
    if ( pWorker->pMan->pPars->fVerbose )
        Abc_Print( 1, "super_prove: direct GIA probe frame=%d pattern=%d output=%d\n", Frame, Pattern, Output );
    ABC_FREE( pSim );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Fingerprints the private graph for bounded heuristic caches.]

  Description [A collision can skip a probe but cannot establish a result.]

  SideEffects []

  SeeAlso     [Cec_SuperProbeDirect]

***********************************************************************/
static int Cec_SuperModelHash( Cec_SuperWorker_t * pWorker, word * pHash )
{
    Gia_Man_t * pGia = pWorker->pGia;
    Gia_Obj_t * pObj;
    word Hash = Gia_ManObjNum(pGia), Prime = ABC_CONST(1099511628211);
    int i;
    Hash = (Hash ^ Gia_ManCiNum(pGia)) * Prime;
    Hash = (Hash ^ Gia_ManCoNum(pGia)) * Prime;
    Hash = (Hash ^ Gia_ManRegNum(pGia)) * Prime;
    Gia_ManForEachObj( pGia, pObj, i )
    {
        if ( !(i & 4095) && Cec_SuperStop(pWorker) ) return 0;
        Hash = (Hash ^ (Gia_ObjIsAnd(pObj) ? 2 : Gia_ObjIsCo(pObj) ? 1 : 0)) * Prime;
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
            Hash = (Hash ^ Gia_ObjFaninLit0(pObj, i)) * Prime;
        if ( Gia_ObjIsAnd(pObj) ) Hash = (Hash ^ Gia_ObjFaninLit1(pObj, i)) * Prime;
    }
    *pHash = Hash;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Claims the initial seed-zero rarity search for this model.]

  Description [Worker identity and scheduler seeds do not select the probe.]

  SideEffects [Records the attempt in the manager-owned cache.]

  SeeAlso     [Cec_SuperRarity]

***********************************************************************/
static int Cec_SuperRaritySeedZero( Cec_SuperWorker_t * pWorker )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    word Hash;
    int i, Try = 1;
    if ( !Cec_SuperModelHash(pWorker, &Hash) ) return 0;
    Cec_SuperLock( p );
    for ( i = 0; i < p->nRarSeedEntries && i < 8; i++ )
        if ( p->RarSeedHash[i] == Hash ) { Try = 0; break; }
    if ( Try ) p->RarSeedHash[p->nRarSeedEntries++ % 8] = Hash;
    Cec_SuperUnlock( p );
    return Try;
}

/**Function*************************************************************

  Synopsis    [Skips repeated deterministic probes of an unchanged model.]

  Description [An incomplete probe can run again with a larger budget.
  The fingerprint only selects heuristic work; it never establishes a proof.]

  SideEffects [Records attempted budgets and fully simulated frames.]

  SeeAlso     [Cec_SuperSimulateDirect]

***********************************************************************/
static int Cec_SuperProbeDirect( Cec_SuperWorker_t * pWorker, int nFrames, abctime Budget )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    word Hash;
    int Slot, Result;
    if ( !Cec_SuperModelHash(pWorker, &Hash) ) return -1;
    Cec_SuperLock( p );
    for ( Slot = 0; Slot < p->nDirectEntries && Slot < 8; Slot++ )
        if ( p->DirectHash[Slot] == Hash ) break;
    if ( Slot < p->nDirectEntries && Slot < 8 )
    {
        if ( p->DirectFrames[Slot] >= nFrames ||
             (p->DirectLimit[Slot] >= nFrames && p->DirectBudget[Slot] >= Budget) )
        {
            Cec_SuperUnlock( p );
            if ( p->pPars->fVerbose )
                Abc_Print( 1, "super_prove: skipped repeated direct rarity probe.\n" );
            return -1;
        }
    }
    else
    {
        Slot = p->nDirectEntries++ % 8;
        p->DirectHash[Slot] = Hash;
        p->DirectFrames[Slot] = p->DirectLimit[Slot] = 0;
        p->DirectBudget[Slot] = 0;
    }
    p->DirectLimit[Slot] = Abc_MaxInt( p->DirectLimit[Slot], nFrames );
    if ( p->DirectBudget[Slot] < Budget ) p->DirectBudget[Slot] = Budget;
    Cec_SuperUnlock( p );
    Result = Cec_SuperSimulateDirect( pWorker, nFrames );
    Cec_SuperLock( p );
    if ( p->DirectHash[Slot] == Hash )
        p->DirectFrames[Slot] = Abc_MaxInt( p->DirectFrames[Slot], pWorker->nDirectFrames );
    Cec_SuperUnlock( p );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries complementary rarity depths and seeds on one worker.]

  Description [Eligible single-output models receive a brief seed-zero search.
  Subsequent phases narrow the simulation width while increasing depth,
  following the Python portfolio's rarity schedule. Each phase has both a
  round limit and a time share; narrow phases receive a larger share.
  Other models retain the existing configuration. Candidates are checked
  on the original graph before publication.]

  SideEffects [May attach a candidate trace to the private graph.]

  SeeAlso     [Cec_SuperSolve]

***********************************************************************/
static int Cec_SuperRarity( Cec_SuperWorker_t * pWorker )
{
    Ssw_RarPars_t Pars;
    Gia_Man_t * pGia = pWorker->pGia;
    Abc_Cex_t * pCex;
    abctime Deadline = pWorker->Deadline, Now, Share = (Deadline - Abc_Clock()) / 9;
    int Phase;
    if ( Share < CLOCKS_PER_SEC ) Share = CLOCKS_PER_SEC;
    Ssw_RarSetDefaultParams( &Pars );
    Pars.nRandSeed = pWorker->RarSeed;
    Pars.fSilent = 1;
    Pars.pFuncProgress = Cec_SuperProgress;
    Pars.pProgress = pWorker;
    Pars.TimeOut = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
    if ( Gia_ManRegNum(pGia) > 10000 || Gia_ManAndNum(pGia) >= 250000 || Gia_ManPoNum(pGia) != 1 )
        return Ssw_RarSimulateGia( pGia, &Pars );
    if ( Cec_SuperRaritySeedZero(pWorker) )
    {
        Now = Abc_Clock();
        pWorker->Deadline = Now + CLOCKS_PER_SEC / 2;
        if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
        Pars.nRandSeed = 0;
        pCex = Ssw_RarFindCexGia( pGia, &Pars );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( Cec_SuperRarityCandidate(pWorker, pCex) ) return 0;
        if ( Cec_SuperStop(pWorker) ) return -1;
    }
    Pars.nRandSeed = pWorker->RarSeed;
    Pars.nFrames = 40;
    Pars.nWords = 31;
    Pars.nBinSize = 16;
    Pars.nRounds = 700;
    for ( Phase = 0; !Cec_SuperStop(pWorker); Phase++ )
    {
        Pars.TimeOut = Abc_MaxInt( 1, (int)((Deadline - Abc_Clock() + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC) );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: rarity phase=%d frames=%d words=%d bin=%d seed=%d\n",
                Phase, Pars.nFrames, Pars.nWords, Pars.nBinSize, Pars.nRandSeed );
        Now = Abc_Clock();
        pWorker->Deadline = Now + Share * (Pars.nWords == 1 ? 2 : 1);
        if ( pWorker->Deadline > Deadline ) pWorker->Deadline = Deadline;
        pCex = Ssw_RarFindCexGia( pGia, &Pars );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: rarity phase=%d elapsed=%.3f sec limited=%d candidate=%d\n",
                Phase, (double)(Abc_Clock() - Now) / CLOCKS_PER_SEC, pWorker->fInterrupted, pCex != NULL );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( Cec_SuperRarityCandidate(pWorker, pCex) ) return 0;
        Pars.nRandSeed = (Pars.nRandSeed + 23) % 1000;
        if ( (Phase + 1) % 9 == 0 )
        {
            Pars.nFrames = 40;
            Pars.nWords = 31;
        }
        else
        {
            Pars.nFrames = Abc_MinInt( 2 * Pars.nFrames, 3500 );
            Pars.nWords = Abc_MaxInt( (Pars.nWords + 1) / 2 - 1, 1 );
        }
    }
    return -1;
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
    int Result, Engine = pWorker->Engine;
    if ( pWorker->fInitial && Gia_ManObjNum(pGia) <= 1000000 &&
         ((Engine == SUPER_BMC3_GLUCOSE && pWorker->pMan->fEarlyAbs) ||
          (Engine == SUPER_BMC3_CADICAL && Gia_ManRegNum(pGia) >= 1024)) )
    {
        // Larger BMC instances reuse completed structural preparation.
        // The recipe preserves input/output order and the original frame index.
        pNew = Cec_SuperPrepare( pGia, pWorker, 0, 2, 0 );
        Gia_ManStop( pGia );
        pGia = pNew; Cec_SuperSetGia( pWorker, pGia );
        pNew = NULL;
    }
    Result = Cec_SuperConstant(pGia);
    pWorker->pSolvedBy = Result != -1 ? "trivial" : Cec_ManSuperEngineName( Engine );
    if ( Result != -1 || Cec_SuperStop(pWorker) ) return Result;
    if ( Engine == SUPER_UFAR )
    {
        pWorker->fMerged = 1;
        return Ufar_ProveWithCex( pWorker->pMan->pWlc, pWorker->Seconds, 0,
            Cec_SuperStopId, 0, NULL, &pGia->pCexSeq );
    }
    if ( !Gia_ManRegNum(pGia) )
    {
        pWorker->pSolvedBy = "comb-sat";
        return Cec_SuperComb(pWorker);
    }
    if ( Engine == SUPER_PDR_T_SCORR || Engine == SUPER_RAR_SCNEW )
        return Cec_SuperCorrRace( pWorker );
    if ( Engine == SUPER_PDR2_QUICK || Engine == SUPER_PDR2_T_QUICK || Engine == SUPER_PDR2_SIM_QUICK )
        return Cec_SuperQuickPdr( pWorker );
    if ( Engine == SUPER_PHASE_SCORR ) return Cec_SuperPhaseSolve(pWorker);
    if ( Engine == SUPER_INT_SYN2 ) return Cec_SuperIntSyn2(pWorker);
    if ( Engine == SUPER_PDR2_STARTUP ) return Cec_SuperStartupSolve(pWorker);
    if ( Engine == SUPER_BDD_SIMPLIFY ) return Cec_SuperBddSolve(pWorker);
    if ( Engine == SUPER_PDR2_RPM ) return Cec_SuperRpm(pWorker, 0, 100000, 0);
    if ( Engine == SUPER_PDR2_TEMPORAL || Engine == SUPER_GLA_TEMPORAL )
        return Cec_SuperTemporalSolve( pWorker );
    if ( Engine == SUPER_BMC3_CADICAL_GLUCOSE )
        return Cec_SuperBmcRace( pWorker );
    if ( Engine == SUPER_SYN2_SCORR || Engine == SUPER_RETIME_SCORR )
        return Cec_SuperSyn2Corr( pWorker );
    if ( Gia_ManPoNum(pGia) > 1 && (Engine == SUPER_FLA || Engine == SUPER_INT || Engine == SUPER_INT_OLD ||
         Engine == SUPER_GLA || Engine == SUPER_GLA_PDR ||
         Engine == SUPER_GLA_PDR_ORIGINAL || Engine == SUPER_PDR_T_OR) )
    {
        pNew = Cec_SuperMergeOutputs( pGia );
        Gia_ManStop( pGia );
        pGia = pNew; Cec_SuperSetGia( pWorker, pGia );
        pWorker->fMerged = 1;
        pNew = NULL;
        Result = Cec_SuperConstant( pGia );
        if ( Result != -1 ) { pWorker->pSolvedBy = "trivial"; return Result; }
    }
    if ( Engine == SUPER_PDR2 || Engine == SUPER_PDR2_T || Engine == SUPER_PDR2_SIM )
    {
        Pdr2_Par_t Pars;
        Pdr2_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.pFuncStop = Cec_SuperStopId;
        Pars.fVerifyComplete = 1;
        if ( !pWorker->pMan->pPars->iEngine )
        {
            Pars.nRandomSeed = (int)(37u * (unsigned)pWorker->Generation % 1000u);
            Pars.nBmcTime = 0;
            if ( Engine == SUPER_PDR2 ) Pars.nAbsRuns = 0;
        }
        if ( Engine == SUPER_PDR2_T )
        {
            Pars.fUseAbs = 1;
            Pars.fBlockInduct ^= 1;
        }
        if ( Engine == SUPER_PDR2_SIM )
        {
            // A complementary search uses simulation weakening and relative induction.
            Pars.nBmcTime = 0;
            Pars.nAbsRuns = 0;
            Pars.nLiftSim = 2;
            Pars.nMicMode = 1;
            Pars.fBlockInduct = 1;
        }
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
        Pars.fTsimStop = 1;
        Pars.pFuncStop = Cec_SuperStopId;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Pdr_ManSolve( pAig, &Pars );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_BMC3_CADICAL )
    {
        Bmc_GiaPar_t Pars;
        Bmc_Shared_t Shared = { Cec_SuperBmcFrames, pWorker->pMan };
        Bmc_GiaSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.nMemoryLimit = pWorker->pMan->pPars->nBmcMemory;
        Pars.TimeToStop = pWorker->Deadline;
        Pars.fSilent = 1;
        Pars.pFuncStop = Cec_SuperStop;
        Pars.pStopData = pWorker;
        if ( pWorker->pMan->pPars->iEngine == SUPER_BMC3_CADICAL_GLUCOSE ) Pars.pShared = &Shared;
        Result = Bmc_GiaPerform( pGia, &Pars );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: bmc3-cadical safe=%d shared=%d queries=%d "
                "memory_stop=%d estimated_peak=%.1f MiB\n",
                Pars.nFramesDone, Pars.nFramesShared, Pars.nQueries, Pars.fMemoryLimit, Pars.MemoryPeakMB );
    }
    else if ( Engine == SUPER_BMC3_CLASSIC || Engine == SUPER_BMC3_GLUCOSE )
    {
        Saig_ParBmc_t Pars;
        Bmc_Shared_t Shared = { Cec_SuperBmcFrames, pWorker->pMan };
        Bmc_Stats_t Stats;
        Saig_ParBmcSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.fUseGlucose = Engine == SUPER_BMC3_GLUCOSE;
        Pars.pFuncStop = Cec_SuperStopId;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Saig_ManBmcScalablePortfolio( pAig, &Pars, pWorker->pMan->pPars->nBmcMemory,
            pWorker->pMan->pPars->iEngine == SUPER_BMC3_CADICAL_GLUCOSE ? &Shared : NULL, &Stats );
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: %s safe=%d shared=%d memory_stop=%d estimated_peak=%.1f MiB\n",
                Cec_ManSuperEngineName(Engine), Pars.iFrame + 1, Stats.nFramesShared,
                Stats.fMemoryLimit, Stats.MemoryPeakMB );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_RAR )
    {
        abctime Deadline = pWorker->Deadline, Start = Abc_Clock();
        int fLarge = Gia_ManObjNum(pGia) > 100000 && Gia_ManRegNum(pGia) > 8192;
        abctime ProbeBudget = fLarge ? 8 * (abctime)CLOCKS_PER_SEC : 3 * (abctime)CLOCKS_PER_SEC / 4;
        // Follow narrow trajectories before rarity selection replaces their states.
        if ( Deadline - Start > ProbeBudget ) pWorker->Deadline = Start + ProbeBudget;
        Result = Cec_SuperProbeDirect( pWorker, fLarge ? 4096 : 1024, pWorker->Deadline - Start );
        pWorker->Deadline = Deadline;
        pWorker->fInterrupted = 0;
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: rarity direct probe result=%d elapsed=%.6f sec\n",
                Result, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
        if ( Result == 0 || Cec_SuperStop(pWorker) ) return Result;
        if ( pWorker->pMan->pPars->fVerbose )
            Abc_Print( 1, "super_prove: rarity seed=%d model=%d\n", pWorker->RarSeed, pWorker->Generation );
        Result = Cec_SuperRarity( pWorker );
    }
    else if ( Engine == SUPER_SIM4 )
    {
        Ssw_ParSim4_t Pars;
        Ssw_Sim4SetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.TimeToStop = pWorker->Deadline;
        Pars.nMemoryLimit = 2048;
        Pars.fSilent = 1;
        Pars.pFuncStop = Cec_SuperStop;
        Pars.pStopData = pWorker;
        Result = Ssw_Sim4Perform( pGia, &Pars );
        if ( Result != 0 ) Result = -1;
    }
    else if ( Engine == SUPER_KIND )
    {
        Cec_ParKind_t Pars;
        Cec_ManKindSetDefaultParams( &Pars );
        Pars.nTimeOutMs = 1000 * pWorker->Seconds;
        Pars.TimeToStop = pWorker->Deadline;
        Pars.nAndMax = 0;
        Pars.nFramesMax = 8;
        Pars.nConfLimit = 0;
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
        Result = Imc_ManPerformWithStop( pGia, &Pars, Cec_SuperStop, pWorker );
    }
    else if ( Engine == SUPER_INT_OLD )
    {
        Inter_ManParams_t Pars;
        int Frame;
        if ( !Gia_ManPiNum(pGia) ) return -1;
        Inter_ManSetDefaultParams( &Pars );
        Pars.nSecLimit = pWorker->Seconds;
        Pars.TimeToStop = pWorker->Deadline;
        Pars.pFuncStop = Cec_SuperStopId;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Inter_ManPerformInterpolation( pAig, &Pars, &Frame );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
        if ( Result == 0 && !pGia->pCexSeq ) Result = -1;
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
        Vec_IntFreeP( &pWorker->vGlaClasses );
        pWorker->fGlaSat = 0;
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
    else if ( Engine == SUPER_SCNEW || Engine == SUPER_SCORR3 || Engine == SUPER_SCORR4 )
    {
        Cec_ParCor_t Pars;
        Cec_ManCorSetDefaultParams( &Pars );
        Pars.nProcs = 1;
        Pars.nBTLimit = Engine == SUPER_SCNEW ? 100 : 1000;
        if ( Engine == SUPER_SCNEW ) Pars.nLevelMax = 100;
        Pars.pFunc = (void *)Cec_SuperStop;
        Pars.pData = pWorker;
        pNew = Engine == SUPER_SCNEW ? Cec_ManLSCorrespondence(pGia, &Pars) :
            Engine == SUPER_SCORR3 ? Cec_ManLSCorrespondence3(pGia, &Pars)
                                    : Cec_ManLSCorrespondence4(pGia, &Pars, 4, 0);
    }
    else if ( Engine == SUPER_DRWSAT )
        pNew = Drw_ManRwsatWithStop( pGia, 0, 0, Cec_SuperStop, pWorker );
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
        pGia = pNew; Cec_SuperSetGia( pWorker, pGia );
        Result = Cec_SuperConstant( pGia );
        if ( Result != -1 ) return Result;
        if ( Engine != SUPER_DRWSAT && !pWorker->fRaw &&
             pWorker->pMan->pPars->fRewrite && !Cec_SuperStop(pWorker) )
        {
            pNew = Drw_ManRwsatWithStop( pGia, 0, 0, Cec_SuperStop, pWorker );
            if ( pNew ) { Gia_ManStop(pGia); pGia = pNew; Cec_SuperSetGia( pWorker, pGia ); }
            Result = Cec_SuperConstant( pGia );
            if ( Result != -1 ) return Result;
        }
        Cec_SuperReduce( pWorker, Gia_ManDup(pGia) );
        if ( pWorker->pMan->pPars->iEngine && !pWorker->fRaw && !Cec_SuperStop(pWorker) )
        {
            pWorker->Engine = SUPER_PDR2;
            Result = Cec_SuperSolve( pWorker );
            pWorker->Engine = Engine;
        }
    }
    return Result == 0 || Result == 1 ? Result : -1;
}

/**Function*************************************************************

  Synopsis    [Starts complementary searches before longer reduction passes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperSchedule( Cec_SuperMan_t * p )
{
    static const int Engines[] = { SUPER_KIND, SUPER_GLA_PDR, SUPER_PDR2_T_QUICK,
        SUPER_RAR, SUPER_BMC3_GLUCOSE, SUPER_PDR2_QUICK,
        SUPER_SCORR4, SUPER_SYN2_SCORR, SUPER_BMC3_CADICAL, SUPER_SIM4, SUPER_PDR_T_SCORR,
        SUPER_GLA_PDR_ORIGINAL,
        SUPER_INT_OLD, SUPER_FLA, SUPER_SCORR, SUPER_PDR_T, SUPER_SCORR3, SUPER_PDR, SUPER_BMC3_CLASSIC };
    int i, Engine, fSmall = Gia_ManAndNum(p->pInitial) < 10000;
    int fMulti = Gia_ManPoNum(p->pInitial) > 1;
    int fTemporal = Gia_ManPoNum(p->pInitial) == 1 && Gia_ManRegNum(p->pInitial) <= 256 &&
        Gia_ManAndNum(p->pInitial) < 100000 && p->pPars->nProcs >= 4;
    p->fRpmEarly = !p->fEarlyAbs && !fMulti && p->pPars->nProcs >= 6 &&
        Gia_ManRegNum(p->pInitial) <= 1024 && Gia_ManAndNum(p->pInitial) < 30000 &&
        Gia_ManPiNum(p->pInitial) > Gia_ManRegNum(p->pInitial);
    int fPhaseEarly = fTemporal && !fMulti && Gia_ManPiNum(p->pInitial) <= Gia_ManRegNum(p->pInitial) &&
        Gia_ManAndNum(p->pInitial) < 10000;
    p->Head = p->Tail = 0;
    if ( p->pPars->iEngine )
        p->Queue[p->Tail++] = p->pPars->iEngine;
    else
    {
        if ( p->pWlc && p->pWlc->nObjs[WLC_OBJ_ARI_MULTI] )
            p->Queue[p->Tail++] = SUPER_UFAR;
        if ( p->fComb )
        {
            p->Queue[p->Tail++] = SUPER_COMB;
            return;
        }
        for ( i = 0; i < (int)(sizeof(Engines) / sizeof(int)); i++ )
        {
            if ( i == 6 && p->fRpmEarly ) p->Queue[p->Tail++] = SUPER_PDR_T_SCORR;
            Engine = Engines[i];
            // Keep both persistent concrete searches in the opening six tasks.
            if ( fSmall )
            {
                if ( Engine == SUPER_KIND ) Engine = SUPER_PDR2_QUICK;
                else if ( Engine == SUPER_PDR2_QUICK ) Engine = SUPER_KIND;
            }
            if ( !p->fEarlyAbs )
            {
                if ( Engine == SUPER_PDR2_T_QUICK ) Engine = SUPER_PDR_T_SCORR;
                else if ( Engine == SUPER_PDR_T_SCORR ) Engine = SUPER_PDR2_T_QUICK;
            }
            if ( fMulti )
            {
                if ( Engine == SUPER_GLA_PDR ) Engine = SUPER_SCORR4;
                else if ( Engine == SUPER_SCORR4 ) Engine = SUPER_GLA_PDR;
            }
            if ( fPhaseEarly && Engine == SUPER_GLA_PDR ) Engine = SUPER_PHASE_SCORR;
            if ( Gia_ManRegNum(p->pInitial) > 512 )
            {
                if ( Engine == SUPER_SIM4 ) Engine = SUPER_BMC3_CADICAL;
                else if ( Engine == SUPER_BMC3_CADICAL ) Engine = SUPER_SIM4;
            }
            // Retiming exposes register invariants in larger multi-output cones.
            if ( Engine == SUPER_SYN2_SCORR && fMulti &&
                 Gia_ManRegNum(p->pInitial) >= 512 && Gia_ManRegNum(p->pInitial) <= 10000 &&
                 Gia_ManAndNum(p->pInitial) >= 10000 && Gia_ManAndNum(p->pInitial) <= 100000 )
                Engine = SUPER_RETIME_SCORR;
            // Complement the persistent PDR2 model with a reachable-state prefix.
            if ( Engine == SUPER_INT_OLD && !fMulti && p->pPars->nProcs >= 4 &&
                 Gia_ManRegNum(p->pInitial) >= 4096 && Gia_ManRegNum(p->pInitial) <= 8192 &&
                 Gia_ManAndNum(p->pInitial) >= 100000 && Gia_ManAndNum(p->pInitial) <= 250000 ) Engine = SUPER_INT_SYN2;
            if ( Engine == SUPER_GLA_PDR_ORIGINAL && fTemporal ) Engine = SUPER_GLA_TEMPORAL;
            if ( Engine == SUPER_PDR_T_SCORR && p->fRpmEarly ) Engine = SUPER_PDR2_RPM;
#ifdef ABC_USE_CUDD
            if ( Engine == SUPER_PDR2_RPM && Gia_ManRegNum(p->pInitial) >= 32 &&
                 Gia_ManRegNum(p->pInitial) <= 128 && Gia_ManAndNum(p->pInitial) >= 1000 &&
                 Gia_ManAndNum(p->pInitial) < 10000 )
                Engine = SUPER_BDD_SIMPLIFY;
#endif
            p->Queue[p->Tail++] = Engine;
            if ( i == 9 )
            {
                if ( fTemporal ) p->Queue[p->Tail++] = SUPER_PDR2_TEMPORAL;
                if ( p->pPars->nProcs >= 4 && Gia_ManRegNum(p->pInitial) <= 10000 &&
                     Gia_ManObjNum(p->pInitial) <= 250000 )
                    p->Queue[p->Tail++] = fPhaseEarly ? SUPER_GLA_PDR : SUPER_PHASE_SCORR;
                if ( !fMulti && p->pPars->nProcs >= 4 &&
                     Gia_ManRegNum(p->pInitial) <= 512 && Gia_ManObjNum(p->pInitial) <= 30000 )
                    p->Queue[p->Tail++] = SUPER_PDR2_STARTUP;
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Queues a deferred or longer attempt without duplicate entries.]

  Description [The caller holds the scheduling mutex.]

  SideEffects [May compact the pending queue.]

  SeeAlso     [Cec_SuperWorker]

***********************************************************************/
static void Cec_SuperEnqueue( Cec_SuperMan_t * p, int Engine, int fPriority )
{
    int i;
    for ( i = p->Head; i < p->Tail; i++ )
        if ( p->Queue[i] == Engine )
        {
            if ( fPriority )
            {
                memmove( p->Queue + p->Head + 1, p->Queue + p->Head, sizeof(int) * (i - p->Head) );
                p->Queue[p->Head] = Engine;
            }
            return;
        }
    if ( p->Tail == SUPER_QUEUE && p->Head )
    {
        memmove( p->Queue, p->Queue + p->Head, sizeof(int) * (p->Tail - p->Head) );
        p->Tail -= p->Head;
        p->Head = 0;
    }
    assert( p->Tail < SUPER_QUEUE );
    if ( fPriority )
    {
        memmove( p->Queue + p->Head + 1, p->Queue + p->Head, sizeof(int) * (p->Tail - p->Head) );
        p->Queue[p->Head] = Engine;
        p->Tail++;
    }
    else p->Queue[p->Tail++] = Engine;
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
        int Position = p->Head;
        if ( p->StartupState != 2 )
            for ( ; Position < p->Tail; Position++ )
                if ( p->Queue[Position] == SUPER_RAR || p->Queue[Position] == SUPER_BMC3_GLUCOSE ||
                     p->Queue[Position] == SUPER_UFAR ) break;
        if ( Position < p->Tail )
        {
            abctime Now = Abc_Clock(), Budget;
            int fOriginal, Retry;
            int Engine = p->Queue[Position];
            memmove( p->Queue + p->Head + 1, p->Queue + p->Head, sizeof(int) * (Position - p->Head) );
            p->Queue[p->Head] = Engine;
            pWorker->Engine = p->Queue[p->Head++];
            if ( !p->pPars->iEngine && pWorker->Engine == SUPER_GLA_TEMPORAL && p->nWorkers < 4 )
                pWorker->Engine = SUPER_GLA_PDR_ORIGINAL;
            if ( !p->pPars->iEngine &&
                 (pWorker->Engine == SUPER_PDR2_RPM || pWorker->Engine == SUPER_BDD_SIMPLIFY) && p->nWorkers < 6 )
                pWorker->Engine = SUPER_PDR_T_SCORR;
            fOriginal = pWorker->Engine == SUPER_BDD_SIMPLIFY ||
                pWorker->Engine == SUPER_PDR2_STARTUP || pWorker->Engine == SUPER_INT_SYN2 ||
                pWorker->Engine == SUPER_PHASE_SCORR ||
                pWorker->Engine == SUPER_PDR2_RPM ||
                pWorker->Engine == SUPER_GLA_PDR_ORIGINAL || pWorker->Engine == SUPER_BMC3_GLUCOSE ||
                pWorker->Engine == SUPER_UFAR || pWorker->Engine == SUPER_INT_OLD ||
                pWorker->Engine == SUPER_PDR2_QUICK || pWorker->Engine == SUPER_PDR2_T_QUICK ||
                pWorker->Engine == SUPER_PDR2_SIM_QUICK || pWorker->Engine == SUPER_PDR2_TEMPORAL ||
                pWorker->Engine == SUPER_GLA_TEMPORAL ||
                pWorker->Engine == SUPER_BMC3_CADICAL || pWorker->Engine == SUPER_BMC3_CADICAL_GLUCOSE ||
                pWorker->Engine == SUPER_RAR || pWorker->Engine == SUPER_RAR_SCNEW ||
                (pWorker->Engine == SUPER_PDR_T_SCORR && (p->pPars->iEngine || !p->fEarlyAbs)) ||
                pWorker->Engine == SUPER_SIM4 || pWorker->Engine == SUPER_SYN2_SCORR ||
                pWorker->Engine == SUPER_RETIME_SCORR;
            if ( !p->pPars->iEngine )
            {
                // Reserve a bounded complementary search for the available graph size.
                if ( pWorker->Engine == SUPER_BMC3_CADICAL &&
                     (p->nWorkers < 4 || Gia_ManRegNum(p->pInitial) > 2048) ) continue;
                if ( pWorker->Engine == SUPER_SIM4 && p->nWorkers < 4 ) continue;
                if ( pWorker->Engine == SUPER_INT_SYN2 && p->nWorkers < 4 ) continue;
                if ( pWorker->Engine == SUPER_PHASE_SCORR && p->nWorkers < 4 ) continue;
                if ( pWorker->Engine == SUPER_PDR2_STARTUP && p->nWorkers < 4 ) continue;
                if ( pWorker->Engine == SUPER_PDR2_TEMPORAL && p->nWorkers < 4 ) continue;
                if ( pWorker->Engine == SUPER_SYN2_SCORR && Gia_ManObjNum(p->pInitial) > 100000 ) continue;
            }
            pWorker->Generation = fOriginal ? 0 : p->Generation;
            if ( p->Running[pWorker->Engine] )
            {
                if ( p->Started[pWorker->Engine] < pWorker->Generation )
                    p->Deferred[pWorker->Engine] = 1;
                continue;
            }
            Retry = p->Started[pWorker->Engine] == pWorker->Generation ? p->RetryBudget[pWorker->Engine] : 0;
            if ( p->Started[pWorker->Engine] >= pWorker->Generation && !Retry ) continue;
            p->RetryBudget[pWorker->Engine] = 0;
            p->Started[pWorker->Engine] = pWorker->Generation;
            p->Running[pWorker->Engine] = 1;
            pWorker->fInterrupted = 0;
            pWorker->fMerged = 0;
            if ( pWorker->Engine == SUPER_RAR || pWorker->Engine == SUPER_RAR_SCNEW )
                pWorker->RarSeed = (113 + 23 * p->nRarRuns++) % 1000;
            pWorker->fPersistent = !p->pPars->iEngine &&
                ((p->fPersistentBmc && pWorker->Engine == SUPER_BMC3_GLUCOSE) ||
                 (p->fPersistentPdr && pWorker->Engine == SUPER_PDR2_QUICK) ||
                 (p->fPersistentExtra && ((p->fRpmEarly ?
                    (pWorker->Engine == SUPER_PDR2_RPM || pWorker->Engine == SUPER_BDD_SIMPLIFY) :
                    pWorker->Engine == (p->fEarlyAbs ? SUPER_PDR2_T_QUICK : SUPER_PDR_T_SCORR)) ||
                    pWorker->Engine == SUPER_RAR)));
            Budget = pWorker->fPersistent || pWorker->Engine == SUPER_COMB ||
                p->pPars->iEngine ? p->Deadline - Now : (abctime)15 * CLOCKS_PER_SEC;
            if ( !p->pPars->iEngine && !pWorker->fPersistent )
            {
                if ( pWorker->Engine == SUPER_SCORR4 ) Budget = (abctime)5 * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_GLA_PDR || pWorker->Engine == SUPER_GLA_PDR_ORIGINAL )
                    Budget = (abctime)10 * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_INT_OLD ) Budget = (abctime)8 * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_KIND ) Budget = (abctime)2 * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_UFAR ) Budget = (abctime)30 * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_SIM4 )
                    Budget = (abctime)(Gia_ManRegNum(p->pInitial) > 512 &&
                        Gia_ManRegNum(p->pInitial) <= 2048 ? 5 : 15) * CLOCKS_PER_SEC;
                if ( pWorker->Engine == SUPER_SYN2_SCORR && Gia_ManAndNum(p->pInitial) < 10000 )
                    Budget = (abctime)3 * CLOCKS_PER_SEC;
                if ( Retry ) Budget = (abctime)Retry * CLOCKS_PER_SEC;
                if ( p->nWorkers < 4 && pWorker->Engine != SUPER_PDR_T_OR )
                {
                    abctime Share = (p->Deadline - p->Start) / (p->nWorkers == 1 ? 8 : 4);
                    if ( !Retry && Budget > Share ) Budget = Share;
                }
            }
            pWorker->Deadline = Now + Budget;
            if ( pWorker->Deadline > p->Deadline ) pWorker->Deadline = p->Deadline;
            pWorker->Seconds = (int)((pWorker->Deadline - Now + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC);
            pWorker->Seconds = Abc_MaxInt( 1, pWorker->Seconds );
            // Gia_ManDup writes Value in its source. Keep copies serialized.
            Cec_SuperSetGia( pWorker, Gia_ManDup(fOriginal ? p->pInitial :
                pWorker->Engine == SUPER_KIND && pWorker->Generation == 0 ? p->pKind : p->pBest) );
            pWorker->fInitial = fOriginal;
            Abc_CexFreeP( &pWorker->pGia->pCexSeq );
            p->Active++;
            p->ActivePersistent += pWorker->fPersistent;
            p->pPars->nStarted++;
            HaveTask = 1;
            if ( p->pPars->fVerbose )
                Abc_Print( 1, "super_prove: start worker=%d engine=%s model=%d source=%s budget=%.3f sec\n",
                    pWorker->Id, Cec_ManSuperEngineName(pWorker->Engine), pWorker->Generation,
                    fOriginal ? "initial" : pWorker->Engine == SUPER_KIND && pWorker->Generation == 0 ?
                        "unswept" : p->pSource,
                    (double)(pWorker->Deadline - Now) / CLOCKS_PER_SEC );
            break;
        }
        if ( !p->Active && p->StartupState == 2 )
        {
            p->Done = 1;
            Cec_SuperRequestStop( p );
            break;
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

  Synopsis    [Builds one startup model while independent searches are running.]

  Description [One elected worker owns rewriting and sweeping. The unswept
  rewrite remains available for induction. The immutable final copy seeds
  initial-model preparation and the large-model PDR fallback.]

  SideEffects [Publishes private copies under the mutex and wakes waiting workers.]

  SeeAlso     [Cec_SuperWorker Cec_SuperPrepare Cec_SuperNext]

***********************************************************************/
static void Cec_SuperStartup( Cec_SuperWorker_t * pWorker )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pModel, * pNext, * pKind;
    abctime Start = Abc_Clock(), Stage, Rewrite = 0, Sweep = 0;
    int fRewriteDone = !p->pPars->fRewrite, fSweepDone = 0, fSmaller = 0;
    const char * pSource = "original";
    pWorker->Deadline = p->Deadline;
    Cec_SuperLock( p );
    pModel = Gia_ManDup( p->pInitial );
    Cec_SuperUnlock( p );
    if ( p->pPars->fRewrite && !Cec_SuperStop(pWorker) )
    {
        Stage = Abc_Clock();
        pNext = Drw_ManRwsatWithStop( pModel, 0, 0, Cec_SuperStop, pWorker );
        Rewrite = Abc_Clock() - Stage;
        if ( pNext && !pWorker->fInterrupted )
        {
            Gia_ManStop( pModel );
            pModel = pNext;
            fRewriteDone = 1;
            pSource = "drwsat";
        }
        else Gia_ManStopP( &pNext );
    }
    // Induction must keep the state removed by the later structural sweep.
    pKind = Gia_ManDup( pModel );
    if ( !Cec_SuperStop(pWorker) )
    {
        Stage = Abc_Clock();
        if ( p->Deadline - Stage > 2 * (abctime)CLOCKS_PER_SEC )
            pWorker->Deadline = Stage + 2 * (abctime)CLOCKS_PER_SEC;
        pNext = Gia_ManSeqStructSweepWithStop( pModel, 1, 1, 0, Cec_SuperStop, pWorker );
        Sweep = Abc_Clock() - Stage;
        fSweepDone = pNext && !pWorker->fInterrupted;
        if ( fSweepDone && (Gia_ManAndNum(pNext) < Gia_ManAndNum(pModel) ||
                           Gia_ManRegNum(pNext) < Gia_ManRegNum(pModel)) )
        {
            Gia_ManStop( pModel );
            pModel = pNext;
            fSmaller = 1;
            pSource = "sweep";
        }
        else Gia_ManStopP( &pNext );
    }
    pWorker->Deadline = p->Deadline;
    pWorker->fInterrupted = 0;
    if ( !Gia_ManIsNormalized(pModel) )
    {
        pNext = Gia_ManDupNormalize( pModel, 1 );
        Gia_ManStop( pModel );
        pModel = pNext;
    }
    Cec_SuperLock( p );
    p->pStartup = pModel;
    Gia_ManStop( p->pBest );
    p->pBest = Gia_ManDup( pModel );
    Gia_ManStop( p->pKind );
    p->pKind = pKind;
    p->pSource = pSource;
    p->pPars->nReduced += (fRewriteDone && p->pPars->fRewrite) + fSmaller;
    if ( !(p->fEarlyAbs && Gia_ManObjNum(p->pInitial) <= 1000000) )
    {
        assert( p->PrepareState[0] == 0 );
        p->pPrepared[0] = Gia_ManDup( pModel );
        // A completed startup rewrite supplies the final sweep's input directly.
        p->PrepareSteps[0] = fRewriteDone ? (fSweepDone ? 3 : 2) : 0;
        p->PrepareLimit[0] = fRewriteDone && !fSweepDone ? Sweep : 0;
        p->PrepareState[0] = 2;
    }
    // In the complementary class BMC may already be building or using the
    // sweep-before-rewrite cache. Startup neither replaces nor invalidates it.
    p->StartupState = 2;
    Cec_SuperWake( p );
    Cec_SuperUnlock( p );
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "super_prove: startup model and=%d ff=%d rewrite=%.6f sweep=%.6f elapsed=%.6f sec\n",
            Gia_ManAndNum(pModel), Gia_ManRegNum(pModel), (double)Rewrite / CLOCKS_PER_SEC,
            (double)Sweep / CLOCKS_PER_SEC, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
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
    int fStartup;
    s_pSuperWorker = pWorker;
    Cec_SuperLock( p );
    fStartup = p->StartupState == 0;
    if ( fStartup ) p->StartupState = 1;
    Cec_SuperUnlock( p );
    if ( fStartup ) Cec_SuperStartup( pWorker );
    while ( Cec_SuperNext(pWorker) )
    {
        abctime Start = Abc_Clock(), CpuStart = p->pPars->fVerbose ? Abc_ThreadClock() : 0;
        int Result = Cec_SuperSolve( pWorker );
        if ( Result >= 0 ) Cec_SuperPublish( pWorker, Result );
        Abc_CexFreeP( &pWorker->pCheckedCex );
        Gia_ManStopP( &pWorker->pGia );
        pWorker->fInitial = 0;
        Vec_IntFreeP( &pWorker->vGlaClasses );
        Cec_SuperLock( p );
        p->Active--;
        p->ActivePersistent -= pWorker->fPersistent;
        p->Running[pWorker->Engine] = 0;
        if ( p->Result < 0 && !p->pPars->iEngine && !pWorker->fPersistent )
        {
            if ( p->Deferred[pWorker->Engine] && p->Started[pWorker->Engine] < p->Generation )
                Cec_SuperEnqueue( p, pWorker->Engine, 1 );
            else if ( Result < 0 && p->Started[pWorker->Engine] <= pWorker->Generation &&
                      Abc_Clock() >= pWorker->Deadline && pWorker->Deadline < p->Deadline )
            {
                p->RetryBudget[pWorker->Engine] = Abc_MinInt( 86400, 2 * pWorker->Seconds );
                Cec_SuperEnqueue( p, pWorker->Engine, 0 );
            }
            p->Deferred[pWorker->Engine] = 0;
        }
        assert( p->Active >= p->ActivePersistent && p->ActivePersistent >= 0 && p->ActivePersistent <= 4 );
        Cec_SuperWake( p );
        if ( p->pPars->fVerbose )
            Abc_Print( 1, "super_prove: stop worker=%d engine=%s result=%d elapsed=%.3f sec cpu=%.3f sec\n",
                pWorker->Id, Cec_ManSuperEngineName(pWorker->Engine), Result,
                (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC,
                (double)(Abc_ThreadClock() - CpuStart) / CLOCKS_PER_SEC );
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
static int Cec_SuperProve( Gia_Man_t * pGia, Wlc_Ntk_t * pWlc, Cec_ParSuper_t * pPars )
{
    Cec_SuperMan_t Man, * p = &Man;
    Cec_SuperWorker_t * pWorkers;
    int i, nWorkers, nCreated = 0, Result;
#ifdef SUPER_USE_PTHREADS
    pthread_t * pThreads;
#endif
    if ( !pGia || !pPars || pPars->nProcs < 1 || pPars->nProcs > 256 ||
         pPars->nTimeOut < 1 || pPars->nTimeOut > 86400 ||
         pPars->nBmcMemory < 0 || pPars->nBmcMemory > 65536 ||
         pPars->iEngine < 0 || pPars->iEngine >= SUPER_ENGINES ||
         (pPars->iEngine == SUPER_UFAR && !pWlc) ||
         pGia->nConstrs || !Abs2_ManCheckZeroInit(pGia) ||
         Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) ) return -2;
    pPars->pWinner = NULL;
    pPars->nStarted = pPars->nReduced = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    Abc_CexFreeP( &pGia->pCexComb );
    memset( p, 0, sizeof(*p) );
    for ( i = 0; i <= SUPER_ENGINES; i++ ) p->Started[i] = -1;
    p->Start = Abc_Clock();
    Result = Cec_SuperConstant( pGia );
    if ( Result != -1 )
    {
        pPars->pWinner = "trivial";
        Cec_SuperReport( pGia, pPars, Result, p->Start );
        return Result;
    }
    p->pOriginal = pGia;
    p->pWlc = pWlc;
    // &miter can interleave new XOR gates and outputs. Normalize and hash
    // only the private solver model, preserving the original PI/PO order.
    p->pInitial = Gia_ManDupNormalize( pGia, 1 );
    p->pPars = pPars;
    p->pSource = "original";
    p->Result = -1;
    p->Deadline = p->Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC;
    p->pBest = Gia_ManDup( p->pInitial );
    p->pKind = Gia_ManDup( p->pInitial );
    p->StartupState = pPars->iEngine ? 2 : 0;
    // Select the complementary persistent proof by interface size.
    p->fEarlyAbs = Gia_ManRegNum(p->pInitial) >= 1024 &&
        Gia_ManPiNum(p->pInitial) >= Gia_ManRegNum(p->pInitial);
    p->fComb = !Gia_ManRegNum(p->pBest);
    Cec_SuperSchedule( p );
    nWorkers = pPars->iEngine ? 1 : Abc_MinInt(pPars->nProcs, p->Tail);
#ifndef SUPER_USE_PTHREADS
    nWorkers = 1;
#endif
    p->nWorkers = 1;
    pWorkers = ABC_CALLOC( Cec_SuperWorker_t, nWorkers );
    for ( i = 0; i < nWorkers; i++ )
    {
        pWorkers[i].pMan = p;
        pWorkers[i].Id = i;
    }
#ifdef SUPER_USE_PTHREADS
    if ( pthread_mutex_init(&p->Mutex, NULL) )
    {
        ABC_FREE(pWorkers); Gia_ManStop(p->pBest); Gia_ManStop(p->pInitial); Gia_ManStop(p->pKind);
        return -3;
    }
    if ( pthread_cond_init(&p->Cond, NULL) )
    {
        pthread_mutex_destroy(&p->Mutex);
        ABC_FREE(pWorkers); Gia_ManStop(p->pBest); Gia_ManStop(p->pInitial); Gia_ManStop(p->pKind);
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
    p->fPersistentPdr = nCreated + 1 >= 4;
    p->fPersistentExtra = nCreated + 1 >= 6;
    p->nWorkers = nCreated + 1;
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
    Gia_ManStopP( &p->pStartup );
    Gia_ManStop( p->pKind );
    Gia_ManStopP( &p->pCorr );
    Gia_ManStopP( &p->pPrepared[0] );
    Gia_ManStopP( &p->pPrepared[1] );
    ABC_FREE( pWorkers );
    if ( Result >= 0 && pPars->fVerbose )
        Abc_Print( 1, "super_prove: answer=%.6f sec shutdown=%.6f sec\n",
            (double)(p->SolvedAt - p->Start) / CLOCKS_PER_SEC,
            (double)(Abc_Clock() - p->SolvedAt) / CLOCKS_PER_SEC );
    Cec_SuperReport( pGia, pPars, Result, p->Start );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Proves a bit-level miter without relying on word-level state.]

  Description []

  SideEffects [Stores a checked counterexample in the input graph.]

  SeeAlso     [Cec_WlcSuperProve]

***********************************************************************/
int Cec_GiaSuperProve( Gia_Man_t * pGia, Cec_ParSuper_t * pPars )
{
    return Cec_SuperProve( pGia, NULL, pPars );
}

/**Function*************************************************************

  Synopsis    [Constructs matching word-level and bit-level proof inputs.]

  Description [A private word-level design belongs exclusively to the UFAR
  lane. Creating the miter here prevents proofs from a stale word-level
  design from being applied to an unrelated current AIG.]

  SideEffects [Returns an owned bit-level miter, even when the proof is undecided.]

  SeeAlso     [Cec_GiaSuperProve]

***********************************************************************/
int Cec_WlcSuperProve( Wlc_Ntk_t * pWlc, Cec_ParSuper_t * pPars, Gia_Man_t ** ppGia )
{
    Wlc_Ntk_t * pCopy;
    Gia_Man_t * pRaw;
    int Result;
    if ( !ppGia ) return -2;
    *ppGia = NULL;
    if ( !pWlc || !pPars || Wlc_NtkPoNum(pWlc) != 2 ||
         Wlc_ObjRange(Wlc_NtkPo(pWlc, 0)) != Wlc_ObjRange(Wlc_NtkPo(pWlc, 1)) ) return -2;
    pCopy = Wlc_NtkDupDfsSimple( pWlc );
    if ( !pCopy ) return -2;
    if ( !Wlc_NtkHasNameId(pCopy) && Wlc_NtkHasNameId(pWlc) ) Wlc_NtkTransferNames( pCopy, pWlc );
    pRaw = Wlc_NtkBitBlast( pCopy, NULL );
    if ( !pRaw ) { Wlc_NtkFree(pCopy); return -2; }
    *ppGia = Gia_ManTransformMiter2( pRaw );
    Gia_ManStop( pRaw );
    Result = Cec_SuperProve( *ppGia, pCopy, pPars );
    Wlc_NtkFree( pCopy );
    return Result;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
