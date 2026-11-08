/**CFile****************************************************************

  FileName    [absFla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Abstraction package.]

  Synopsis    [Scalable flop-level abstraction with PDR2.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 21, 2026.]

  Revision    [$Id: absFla.c,v 1.00 2026/10/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abs2.h"
#include "aig/gia/giaAig.h"
#include "proof/pdr2/pdr2.h"
#include "opt/drw/drw.h"
#include <limits.h>

#if defined(ABC_USE_PTHREADS) && ABC_HAS_THREAD_LOCAL
#define FLA_USE_PTHREADS
#if defined(_WIN32) && !defined(__MINGW32__)
#include "../lib/pthread.h"
#else
#include <pthread.h>
#endif
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Fla_Man_t_ Fla_Man_t;
struct Fla_Man_t_
{
    // user data
    Gia_Man_t *    pGia;          // original design, retained throughout
    Fla_Par_t *    pPars;         // parameters and statistics
    abctime        clkStart;      // wall-clock start
    abctime        clkStop;       // shared deadline, zero if unlimited
    // abstraction
    Abs2_Man_t *   pAbs;          // persistent CaDiCaL unrolling
    Vec_Int_t *    vLast;         // map of the previous proved BMC prefix
    Vec_Int_t *    vProve;        // immutable map of the prover's abstraction
    Vec_Int_t *    vPiMap;        // reduced PI index -> full abstraction PI
    Abc_Cex_t *    pCex;          // independently checked original CEX
    Abc_Cex_t *    pCexPending;   // worker trace awaiting the end of BMC CBA
    Vec_Int_t *    vPending;      // immutable map for the deferred trace
    int            fRefined;      // direct CEX feedback strengthened the map
    int            ResultRefine;  // terminal result collected before CBA
    // prover (one worker per invocation)
    Aig_Man_t *    pAigProve;     // worker owns this independent AIG
    Abc_Cex_t *    pCexProve;     // transferred only after joining
    int            iFrameProve;   // originating BMC frame
    int            fJoinable;     // pending prover invocation, command thread owns
    int            fThreaded;     // the current prover has its own thread
    int            fNoThread;     // thread creation failed; use synchronous calls
    int            nSlice;        // growing synchronous budget on the same map
    int            fStop;         // accessed under the mutex
    int            fDone;         // accessed under the mutex
    int            Result;        // published under the mutex
#ifdef FLA_USE_PTHREADS
    pthread_t      Thread;
    pthread_mutex_t Mutex;
#endif
};

// PDR2's callback takes an integer. A thread-local context avoids sharing
// generations or results with GLA or another independent FLA invocation.
static ABC_THREAD_LOCAL Fla_Man_t * s_pFlaWorker = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Accesses the worker's completion and cancellation state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Fla_ManLock( Fla_Man_t * p )
{
#ifdef FLA_USE_PTHREADS
    int Status = pthread_mutex_lock( &p->Mutex );
    assert( Status == 0 );
    (void)Status;
#endif
}

/**Function*************************************************************

  Synopsis    [Releases the mutex protecting worker completion and cancellation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Fla_ManUnlock( Fla_Man_t * p )
{
#ifdef FLA_USE_PTHREADS
    int Status = pthread_mutex_unlock( &p->Mutex );
    assert( Status == 0 );
    (void)Status;
#endif
}

/**Function*************************************************************

  Synopsis    [Checks the common wall-clock deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManTimedOut( Fla_Man_t * p )
{
    return p->clkStop && Abc_Clock() >= p->clkStop;
}

/**Function*************************************************************

  Synopsis    [Checks the common deadline and external stop callback.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManStopped( Fla_Man_t * p )
{
    return Fla_ManTimedOut(p) || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->pStopData));
}

/**Function*************************************************************

  Synopsis    [Reads the published worker result under the mutex.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManReadDone( Fla_Man_t * p, int * pResult )
{
    int fDone;
    Fla_ManLock( p );
    fDone = p->fDone;
    if ( pResult ) *pResult = p->Result;
    Fla_ManUnlock( p );
    return fDone;
}

/**Function*************************************************************

  Synopsis    [Checks cancellation from the abstraction thread.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManStopAbs( void * pData )
{
    Fla_Man_t * p = (Fla_Man_t *)pData;
    return Fla_ManStopped(p);
}

/**Function*************************************************************

  Synopsis    [Yields BMC when a pending worker result needs processing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManYieldAbs( void * pData )
{
    Fla_Man_t * p = (Fla_Man_t *)pData;
    int Result;
    return p->pCexPending || (p->fJoinable && Fla_ManReadDone(p, &Result) && Result >= 0);
}

/**Function*************************************************************

  Synopsis    [Checks cancellation from the PDR2 worker.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManStopProve( int RunId )
{
    Fla_Man_t * p = s_pFlaWorker;
    int fStop;
    assert( p != NULL );
    Fla_ManLock( p );
    fStop = p->fStop;
    Fla_ManUnlock( p );
    return fStop || Fla_ManStopped(p);
}

/**Function*************************************************************

  Synopsis    [Proves an independent snapshot of the flop abstraction.]

  Description [A proof remains valid if the main thread has refined or
  pruned its map. Abstract counterexamples are never original failures.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void * Fla_ManProveThread( void * pData )
{
    Fla_Man_t * p = (Fla_Man_t *)pData;
    Fla_Man_t * pPrevious = s_pFlaWorker;
    abctime clkCpu = p->pPars->fCollectStats && p->fThreaded ? Abc_ThreadClock() : 0;
    Pdr2_Par_t Pars;
    Abc_Cex_t * pCex;
    int Result;
    s_pFlaWorker = p;
    Pdr2_ManSetDefaultParams( &Pars );
    Pars.fSilent = 1;
    Pars.fVerify = 1;
    Pars.fVerifyComplete = 1;
    Pars.pFuncStop = Fla_ManStopProve;
    if ( !p->fThreaded )
        // The in-flight obligation may use one more slice before stopping.
        Pars.nPropLimit = (ABC_INT64_T)1000000 << p->nSlice;
    if ( p->pPars->nProveMode == 1 )
        Pars.fDynamic = Pars.fCtg = 0;
    else if ( p->pPars->nProveMode >= 2 )
        Pars.nDynTime = 0;
    if ( p->pPars->nProveMode >= 3 )
        Pars.fBlockInduct = 1;
    if ( p->pPars->nProveMode >= 4 )
        Pars.fUseAbs = 1;
    if ( p->pPars->nProveMode == 5 )
        Pars.fDynamic = 0;
    Result = Pdr2_ManSolve( p->pAigProve, &Pars );
    pCex = p->pAigProve->pSeqModel;
    p->pAigProve->pSeqModel = NULL;
    Aig_ManStop( p->pAigProve );
    p->pAigProve = NULL;
    // Do not discard a completed proof when cancellation races with it.
    Fla_ManLock( p );
    p->pCexProve = pCex;
    p->Result = Result;
    p->fDone = 1;
    Fla_ManUnlock( p );
    s_pFlaWorker = pPrevious;
    // The owner reads this accumulator only after joining all invocations.
    if ( p->pPars->fCollectStats && p->fThreaded )
        p->pPars->timeProveCpu += Abc_ThreadClock() - clkCpu;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Starts PDR2 after collecting the preceding invocation.]

  Description [Concurrent execution is available in pthread builds.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManProveStart( Fla_Man_t * p, Vec_Int_t * vClasses, int iFrame )
{
    Gia_Man_t * pAbs, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    assert( !p->fJoinable && !p->pCexProve );
    assert( !p->pCexPending );
    if ( Fla_ManStopped(p) ) return -1;
    pAbs = Abs2_ManDerive( p->pGia, vClasses );
    if ( !pAbs ) return -2;
    if ( p->pPars->fRewrite )
    {
        pTemp = Drw_ManRewrite( pAbs, 0, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pAbs );
            pAbs = pTemp;
        }
    }
    Vec_IntFreeP( &p->vPiMap );
    p->vPiMap = Vec_IntAlloc( Gia_ManPiNum(pAbs) );
    if ( p->pPars->fTrimPis ) Gia_ManCreateRefs( pAbs );
    Gia_ManForEachPi( pAbs, pObj, i )
    {
        pObj->fMark0 = p->pPars->fTrimPis && !Gia_ObjRefNum(pAbs, pObj);
        if ( !pObj->fMark0 ) Vec_IntPush( p->vPiMap, i );
    }
    if ( Vec_IntSize(p->vPiMap) < Gia_ManPiNum(pAbs) )
    {
        pAbs = Gia_ManDupMarked( pTemp = pAbs );
        Gia_ManStop( pTemp );
    }
    p->pAigProve = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    p->nSlice = p->vProve && Vec_IntEqual(p->vProve, vClasses) ? Abc_MinInt(p->nSlice + 1, 5) : 0;
    Vec_IntFreeP( &p->vProve );
    p->vProve = Vec_IntDup( vClasses );
    p->iFrameProve = iFrame;
    p->fStop = p->fDone = 0;
    p->Result = -1;
    p->pPars->nProveCalls++;
    p->fJoinable = 1;
#ifdef FLA_USE_PTHREADS
    p->fThreaded = p->pPars->fUseThread && !p->fNoThread;
    if ( p->fThreaded && pthread_create(&p->Thread, NULL, Fla_ManProveThread, p) )
    {
        p->fThreaded = 0;
        p->fNoThread = 1;
        Abc_Print( 1, "FLA could not start the PDR2 worker; using bounded synchronous PDR2 calls.\n" );
    }
#endif
    if ( !p->fThreaded )
        Fla_ManProveThread( p );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Joins the worker and validates its answer on the design.]

  Description [The abstract model preserves original PI order. Only these
  inputs are copied; all original registers start at zero. A spurious
  counterexample leaves the incremental CBA/PBA engine running.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManProveCollect( Fla_Man_t * p, int fCancel, int fRefine )
{
    Abc_Cex_t * pCex, * pOrig;
    int i, f, Entry, nRegs = 0, nPis, Result;
    if ( !p->fJoinable ) return -1;
    if ( fCancel )
    {
        Fla_ManLock( p );
        p->fStop = 1;
        Fla_ManUnlock( p );
    }
#ifdef FLA_USE_PTHREADS
    if ( p->fThreaded )
    {
        int Status = pthread_join( p->Thread, NULL );
        assert( Status == 0 );
        (void)Status;
    }
#endif
    p->fJoinable = 0;
    assert( p->fDone );
    Result = p->Result;
    pCex = p->pCexProve;
    p->pCexProve = NULL;
    if ( Result == 1 )
    {
        if ( pCex )
        {
            Abc_CexFree( pCex );
            return -2;
        }
        p->pPars->iFrameProved = p->iFrameProve;
        return 1;
    }
    if ( Result != 0 )
    {
        Abc_CexFreeP( &pCex );
        return -1;
    }
    Vec_IntForEachEntry( p->vProve, Entry, i ) nRegs += Entry != 0;
    nPis = Gia_ManPiNum(p->pGia) + Gia_ManRegNum(p->pGia) - nRegs;
    if ( !pCex || pCex->iFrame < 0 || pCex->iFrame == INT_MAX ||
         pCex->iPo < 0 || pCex->iPo >= Gia_ManPoNum(p->pGia) ||
         pCex->nRegs != nRegs || pCex->nPis != Vec_IntSize(p->vPiMap) ||
         ((ABC_INT64_T)pCex->iFrame + 1) * nPis + nRegs > INT_MAX ||
         ((ABC_INT64_T)pCex->iFrame + 1) * pCex->nPis + pCex->nRegs != pCex->nBits )
    {
        Abc_CexFreeP( &pCex );
        return -2;
    }
    // Complete unused inputs with zero before refinement and projection.
    // They have no fanouts in the worker's abstraction, so this preserves
    // its counterexample and the original PI/abstract-flop correspondence.
    if ( pCex->nPis != nPis )
    {
        Abc_Cex_t * pFull = Abc_CexAlloc( nRegs, nPis, pCex->iFrame + 1 );
        pFull->iFrame = pCex->iFrame;
        pFull->iPo = pCex->iPo;
        for ( i = 0; i < nRegs; i++ )
            if ( Abc_InfoHasBit(pCex->pData, i) ) Abc_InfoSetBit( pFull->pData, i );
        for ( f = 0; f <= pCex->iFrame; f++ )
            Vec_IntForEachEntry( p->vPiMap, Entry, i )
                if ( Abc_InfoHasBit(pCex->pData, nRegs + f * pCex->nPis + i) )
                    Abc_InfoSetBit( pFull->pData, nRegs + f * nPis + Entry );
        Abc_CexFree( pCex );
        pCex = pFull;
    }
    pOrig = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), pCex->iFrame + 1 );
    pOrig->iPo = pCex->iPo;
    pOrig->iFrame = pCex->iFrame;
    for ( f = 0; f <= pCex->iFrame; f++ )
        for ( i = 0; i < pOrig->nPis; i++ )
            if ( Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + i) )
                Abc_InfoSetBit( pOrig->pData, pOrig->nRegs + f * pOrig->nPis + i );
    if ( Abs2_ManVerifyCex(p->pAbs, pOrig) )
    {
        Abc_CexFree( pCex );
        Abc_CexFreeP( &p->pCex );
        p->pCex = pOrig;
        return 0;
    }
    Abc_CexFree( pOrig );
    p->pPars->nSpurious++;
    if ( p->pPars->fRefineCex && !Fla_ManStopped(p) )
    {
        if ( fRefine )
        {
            int nAdded = Abs2_ManRefine( p->pAbs, pCex, p->vProve );
            Abc_CexFree( pCex );
            if ( nAdded == -2 ) return -2;
            p->fRefined |= nAdded > 0;
        }
        else
        {
            // CBA still owns the SAT model. Keep the trace and its map,
            // and yield only after CBA has consumed and retired the query.
            assert( !p->pCexPending && !p->vPending );
            p->pCexPending = pCex;
            p->vPending = Vec_IntDup( p->vProve );
        }
    }
    else
        Abc_CexFree( pCex );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Applies a deferred worker trace after BMC releases its model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManRefinePending( Fla_Man_t * p )
{
    int nAdded = 0;
    if ( !p->pCexPending ) return -1;
    if ( !Fla_ManStopped(p) )
        nAdded = Abs2_ManRefine( p->pAbs, p->pCexPending, p->vPending );
    Abc_CexFreeP( &p->pCexPending );
    Vec_IntFreeP( &p->vPending );
    p->fRefined |= nAdded > 0;
    return nAdded == -2 ? -2 : -1;
}

/**Function*************************************************************

  Synopsis    [Retires the concurrent prover before BMC refinement.]

  Description [Matches GLA's cancel/join before consuming a SAT model.
  Preserve completed proofs and defer spurious prover traces until the
  BMC model has been consumed and its query has been retired.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fla_ManBeforeRefine( void * pData )
{
    Fla_Man_t * p = (Fla_Man_t *)pData;
    p->fRefined = 1;
    if ( !p->fJoinable ) return 0;
    p->ResultRefine = Fla_ManProveCollect( p, 1, 0 );
    if ( p->ResultRefine != -1 ) return 1;
    // Even if CBA/PBA returns to this map, launch a new prover only after
    // the abstraction has become stable again, as in GLA.
    Vec_IntFreeP( &p->vProve );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sets default parameters for stand-alone flop abstraction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fla_ManSetDefaultParams( Fla_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Fla_Par_t) );
    pPars->nFramesStable = 0;
    pPars->nSatMode = 2;
    pPars->nCutMax = 4;
    pPars->nProveMode = 0;
    pPars->fUsePba = 1;
    pPars->fRefineCex = 1;
    pPars->fTrimPis = 1;
    pPars->iFrame = pPars->iFrameProved = -1;
}

/**Function*************************************************************

  Synopsis    [Performs incremental flop abstraction and verification.]

  Description [Keeps one unrolling and SAT instance across depths. PDR2
  checks abstraction snapshots and its spurious traces refine the flop map.
  Concurrent mode also advances CBA/PBA while proving. A bounded UNSAT
  answer is never accepted as a safety proof. The original graph is
  retained, together with the last (or proved) flop abstraction map.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManPerformFla( Gia_Man_t * pGia, Fla_Par_t * pPars )
{
    Fla_Man_t Man, * p = &Man;
    Abs2_Par_t ParsAbs;
    Vec_Int_t * vClasses;
    int Result = -1, ResultProve, Depth, Stable = 0, i, Entry, fProvedStreak = 0, fConcurrent = 0;
    if ( !pGia || !pPars || !Abs2_ManCheckZeroInit(pGia) || !Gia_ManPoNum(pGia) || Gia_ManConstrNum(pGia) ||
         pPars->nFramesMax < 0 || pPars->nFramesMax > 100000000 ||
         pPars->nTimeOut < 0 || pPars->nConfLimit < 0 || pPars->nFramesStable < 0 ||
         pPars->nCompactDepth < 0 ||
         pPars->nProveMode < 0 || pPars->nProveMode > 5 )
        return -2;
    memset( p, 0, sizeof(Fla_Man_t) );
    p->pGia = pGia;
    p->pPars = pPars;
    p->clkStart = Abc_Clock();
    p->clkStop = pPars->nTimeOut ? p->clkStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    p->Result = -1;
    p->ResultRefine = -1;
    pPars->iFrame = pPars->iFrameProved = -1;
    pPars->nProveCalls = pPars->nSpurious = pPars->nConcrete = 0;
    pPars->timeTotal = 0;
    pPars->timeProveCpu = 0;
#ifdef FLA_USE_PTHREADS
    if ( pthread_mutex_init(&p->Mutex, NULL) ) return -2;
    fConcurrent = pPars->fUseThread;
#else
    if ( pPars->fUseThread )
        Abc_Print( 1, "FLA concurrency requires pthreads and thread-local storage; using bounded synchronous PDR2 calls.\n" );
#endif
    Abs2_SetDefaultParams( &ParsAbs );
    ParsAbs.nFramesMax = -1;
    ParsAbs.nTimeOut = 0;
    ParsAbs.nConfLimit = pPars->nConfLimit;
    ParsAbs.nSatMode = pPars->nSatMode;
    ParsAbs.nCutMax = pPars->nCutMax;
    ParsAbs.nCompactDepth = pPars->nCompactDepth;
    ParsAbs.fUsePba = pPars->fUsePba;
    ParsAbs.fUseStart = pPars->fUseStart;
    ParsAbs.fStopFull = 0;
    ParsAbs.pFuncStop = Fla_ManStopAbs;
    ParsAbs.pFuncYield = fConcurrent ? Fla_ManYieldAbs : NULL;
    ParsAbs.pFuncRefine = fConcurrent ? Fla_ManBeforeRefine : NULL;
    ParsAbs.pStopData = p;
    p->pAbs = Abs2_ManStart( pGia, &ParsAbs );
    if ( !p->pAbs )
    {
        Result = -2;
        goto finish;
    }
    if ( fConcurrent ) p->vLast = Vec_IntDup( Abs2_ManReadClasses(p->pAbs) );
    Abc_CexFreeP( &pGia->pCexSeq );
    if ( pPars->fVerbose )
        Abc_Print( 1, " Frame    FF/Total     Calls  Stable  PDR2   Cex      Time\n" );
    for ( Depth = 0; !pPars->nFramesMax || Depth < pPars->nFramesMax; Depth++ )
    {
        if ( p->fJoinable && Fla_ManReadDone(p, NULL) )
        {
            Result = Fla_ManProveCollect( p, 0, 1 );
            if ( Result != -1 ) break;
        }
        if ( Fla_ManStopAbs(p) ) break;
        Result = Abs2_ManRun( p->pAbs, Depth, 0 );
        pPars->iFrame = ParsAbs.iFrame;
        if ( p->ResultRefine != -1 ) Result = p->ResultRefine;
        if ( Result != -1 ) break;
        Result = Fla_ManRefinePending( p );
        if ( Result != -1 ) break;
        if ( p->fJoinable && Fla_ManReadDone(p, NULL) )
        {
            Result = Fla_ManProveCollect( p, 0, 1 );
            if ( Result != -1 ) break;
        }
        if ( Fla_ManStopped(p) ) break;
        if ( ParsAbs.iFrame < Depth )
        {
            if ( ParsAbs.fYielded ) { Depth--; continue; }
            break;
        }
        vClasses = Abs2_ManReadClasses( p->pAbs );
        if ( fConcurrent )
        {
            // PBA only weakens the next BMC query. It neither invalidates
            // the old worker's proof nor interrupts this stable streak.
            if ( p->fRefined ) Stable = fProvedStreak = 0;
            else Stable++;
        }
        else if ( p->vLast && Vec_IntEqual(p->vLast, vClasses) && !p->fRefined )
            Stable++;
        else
        {
            Vec_IntFreeP( &p->vLast );
            p->vLast = Vec_IntDup( vClasses );
            Stable = 0;
        }
        pPars->nConcrete = 0;
        Vec_IntForEachEntry( vClasses, Entry, i ) pPars->nConcrete += Entry != 0;
        if ( pPars->fVerbose )
            Abc_Print( 1, "%6d %5d/%-7d %7d %7d %5d %5d %9.3f\n", Depth,
                pPars->nConcrete, Gia_ManRegNum(pGia), ParsAbs.nCalls, Stable,
                pPars->nProveCalls, pPars->nSpurious, (double)(Abc_Clock() - p->clkStart) / CLOCKS_PER_SEC );
        // Concurrent proving follows GLA: wait for stable frames after
        // refinement, then run one prover while BMC continues unrolling.
        if ( fConcurrent ) p->fRefined = 0;
        if ( p->fRefined || Stable >= pPars->nFramesStable ||
             (!fConcurrent && pPars->nConcrete == Gia_ManRegNum(pGia)) )
        {
            if ( !p->fJoinable && (!fConcurrent || !fProvedStreak) )
            {
                Result = Fla_ManProveStart( p, vClasses, Depth );
                if ( p->fNoThread )
                {
                    fConcurrent = 0;
                    ParsAbs.pFuncYield = ParsAbs.pFuncRefine = NULL;
                }
                fProvedStreak = 1;
                p->fRefined = 0;
                if ( Result != -1 ) break;
            }
            // A synchronous call is a bounded slice. Consume its CEX now,
            // then advance BMC even when the map is already fully concrete.
            if ( !fConcurrent )
            {
                Result = Fla_ManProveCollect( p, 0, 1 );
                if ( Result != -1 ) break;
            }
        }
    }
finish:
    // Join before freeing any callback state. Accept a proof completed in
    // either cancellation window, including the final timeout cleanup.
    ResultProve = Fla_ManProveCollect( p, 1, 0 );
    if ( Result == -1 ) Result = ResultProve;
    else if ( ResultProve == -2 || (ResultProve >= 0 && Result >= 0 && Result != ResultProve) )
        Result = -2;
    ParsAbs.fVerbose = pPars->fVerbose;
    if ( p->pAbs ) Abs2_ManStop( p->pAbs );
    if ( Result == 1 )
    {
        Vec_IntFreeP( &pGia->vFlopClasses );
        pGia->vFlopClasses = Vec_IntDup( p->vProve );
        if ( !pPars->fSilent )
            Abc_Print( 1, "FLA completed %d frames and proved abstraction derived in frame %d.  ",
                pPars->iFrame + 1, pPars->iFrameProved );
    }
    else if ( Result == 0 )
    {
        if ( p->pCex )
        {
            Abc_CexFreeP( &pGia->pCexSeq );
            pGia->pCexSeq = p->pCex;
            p->pCex = NULL;
        }
        // Both producers independently simulated the original transition
        // relation, including real mux/XOR nodes, before accepting this CEX.
        if ( !pGia->pCexSeq )
            Result = -2;
        else if ( !pPars->fSilent )
            Abc_Print( 1, "True counter-example detected in frame %d.  ", pGia->pCexSeq->iFrame );
    }
    else if ( Result == -1 && !pPars->fSilent )
        Abc_Print( 1, "FLA %s after %d frames.  ", Fla_ManTimedOut(p) ? "reached timeout" : "is undecided", pPars->iFrame + 1 );
    if ( Result == -2 )
    {
        Abc_CexFreeP( &pGia->pCexSeq );
        Abc_Print( -1, "FLA failed; no verification result was accepted.\n" );
    }
    pPars->nConcrete = 0;
    if ( pGia->vFlopClasses )
        Vec_IntForEachEntry( pGia->vFlopClasses, Entry, i ) pPars->nConcrete += Entry != 0;
    pPars->timeTotal = (double)(Abc_Clock() - p->clkStart) / CLOCKS_PER_SEC;
    if ( !pPars->fSilent ) Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    if ( pPars->fVerbose )
        Abc_Print( 1, "FLA: %d/%d concrete registers, %d PDR2 calls, %d spurious CEXes; SAT = %.3f sec, refinement = %.3f sec.\n",
            pPars->nConcrete, Gia_ManRegNum(pGia), pPars->nProveCalls, pPars->nSpurious, ParsAbs.timeSat, ParsAbs.timeRefine );
    Vec_IntFreeP( &p->vLast );
    Vec_IntFreeP( &p->vProve );
    Vec_IntFreeP( &p->vPiMap );
    Vec_IntFreeP( &p->vPending );
    Abc_CexFreeP( &p->pCex );
    Abc_CexFreeP( &p->pCexPending );
#ifdef FLA_USE_PTHREADS
    {
        int Status = pthread_mutex_destroy( &p->Mutex );
        assert( Status == 0 );
        (void)Status;
    }
#endif
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
