/**CFile****************************************************************

  FileName    [cecSplit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Cofactoring for combinational miters.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSplit.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <math.h>
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"

#include "sat/bmc/bmc.h"
#include "proof/pdr/pdr.h"
#include "proof/cec/cec.h"
#include "proof/ssw/ssw.h"
#include "proof/abs/abs.h"


#ifdef ABC_USE_PTHREADS

#if defined(_WIN32) && !defined(__MINGW32__)
#include "../lib/pthread.h"
#else
#include <pthread.h>
#include <unistd.h>
#endif

#endif

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Ssw_RarSimulateGia( Gia_Man_t * p, Ssw_RarPars_t * pPars );
extern int Bmcg_ManPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars );

typedef struct Par_Share_t_ Par_Share_t;
typedef struct Par_ThData_t_ Par_ThData_t;
static int Cec_SProveCallback( void * pUser, int fSolved, unsigned Result );

typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;
extern int Ufar_ProveWithTimeout( Wlc_Ntk_t * pNtk, int nTimeOut, int fVerbose, int (*pFuncStop)(int), int RunId );

#ifndef ABC_USE_PTHREADS

int Cec_GiaProveTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent ) { return -1; }

#else // pthreads are used

#define PAR_THR_MAX 8
#define PAR_ENGINE_UFAR 6
#define PAR_ENGINE_SCORR1 7
#define PAR_ENGINE_SCORR2 8
#define PAR_ENGINE_GLA 9
struct Par_Share_t_
{
    volatile int       fSolved;
    volatile unsigned  Result;
    volatile int       iEngine;
};
typedef struct Par_ThData_t_
{
    Gia_Man_t * p;
    int         iEngine;
    int         fWorking;
    int         nTimeOut;
    int         Result;
    int         fVerbose;
    int         nTimeOutU;
    Wlc_Ntk_t * pWlc;
    Par_Share_t * pShare;
} Par_ThData_t;
typedef struct Cec_ScorrStop_t_
{
    Par_Share_t * pShare;
    abctime TimeToStop;
} Cec_ScorrStop_t;
static volatile Par_Share_t * g_pUfarShare = NULL;
static volatile Par_Share_t * g_pGlaShare = NULL;
static inline const char * Cec_SolveEngineName( int iEngine )
{
    if ( iEngine == 0 ) return "rar";
    if ( iEngine == 1 ) return "bmc";
    if ( iEngine == 2 ) return "pdr";
    if ( iEngine == 3 ) return "bmc-glucose";
    if ( iEngine == 4 ) return "pdr-abs";
    if ( iEngine == 5 ) return "bmcg";
    if ( iEngine == PAR_ENGINE_UFAR ) return "ufar";
    if ( iEngine == PAR_ENGINE_SCORR1 ) return "scorr-new";
    if ( iEngine == PAR_ENGINE_SCORR2 ) return "scorr-old";
    if ( iEngine == PAR_ENGINE_GLA ) return "gla-q";
    return "unknown";
}
static inline void Cec_CopyGiaName( Gia_Man_t * pSrc, Gia_Man_t * pDst )
{
    char * pName = pSrc->pName ? pSrc->pName : pSrc->pSpec;
    if ( pName == NULL )
        return;
    if ( pDst->pName == NULL )
        pDst->pName = Abc_UtilStrsav( pName );
    if ( pDst->pSpec == NULL )
        pDst->pSpec = Abc_UtilStrsav( pName );
}
static inline void Cec_CopyGiaNameToAig( Gia_Man_t * pGia, Aig_Man_t * pAig )
{
    char * pName = pGia->pName ? pGia->pName : pGia->pSpec;
    if ( pName == NULL )
        return;
    if ( pAig->pName == NULL )
        pAig->pName = Abc_UtilStrsav( pName );
    if ( pAig->pSpec == NULL )
        pAig->pSpec = Abc_UtilStrsav( pName );
}
static int Cec_SProveStopUfar( int RunId )
{
    (void)RunId;
    return g_pUfarShare && g_pUfarShare->fSolved != 0;
}
static int Cec_SProveStopGla( int RunId )
{
    (void)RunId;
    return g_pGlaShare && g_pGlaShare->fSolved != 0;
}
static int Cec_ScorrStop( void * pUser )
{
    Cec_ScorrStop_t * p = (Cec_ScorrStop_t *)pUser;
    if ( p == NULL )
        return 0;
    if ( p->pShare && p->pShare->fSolved )
        return 1;
    if ( p->TimeToStop && Abc_Clock() >= p->TimeToStop )
        return 1;
    return 0;
}
static int Cec_SProveCallback( void * pUser, int fSolved, unsigned Result )
{
    Par_ThData_t * pThData = (Par_ThData_t *)pUser;
    Par_Share_t * pShare = pThData ? pThData->pShare : NULL;
    if ( pShare == NULL )
        return 0;
    if ( fSolved )
    {
        if ( pShare->fSolved == 0 )
        {
            pShare->fSolved = 1;
            pShare->Result  = Result;
            pShare->iEngine = pThData->iEngine;
        }
        return 0;
    }
    return pShare->fSolved != 0;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_GiaProveOne( Gia_Man_t * p, int iEngine, int nTimeOut, int fVerbose, Par_ThData_t * pThData )
{
    abctime clk = Abc_Clock();   
    int RetValue = -1;
    if ( iEngine != PAR_ENGINE_UFAR && iEngine != PAR_ENGINE_GLA && Gia_ManRegNum(p) == 0 )
    {
        if ( fVerbose )
            printf( "Engine %d skipped because the current miter is combinational.\n", iEngine );
        return -1;
    }
    //abctime clkStop = nTimeOut * CLOCKS_PER_SEC + Abc_Clock();
    if ( fVerbose )
    printf( "Calling engine %d with timeout %d sec.\n", iEngine, nTimeOut );
    Abc_CexFreeP( &p->pCexSeq );
    if ( iEngine == 0 )
    {
        Ssw_RarPars_t Pars, * pPars = &Pars;
        Ssw_RarSetDefaultParams( pPars );
        pPars->TimeOut = nTimeOut;
        pPars->fSilent = 1;
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        RetValue = Ssw_RarSimulateGia( p, pPars );
    }
    else if ( iEngine == 1 )
    {
        Saig_ParBmc_t Pars, * pPars = &Pars;
        Saig_ParBmcSetDefaultParams( pPars );
        pPars->nTimeOut = nTimeOut;
        pPars->fSilent  = 1;
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        Aig_Man_t * pAig = Gia_ManToAigSimple( p );
        Cec_CopyGiaNameToAig( p, pAig );
        RetValue = Saig_ManBmcScalable( pAig, pPars );
        p->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );                 
    }
    else if ( iEngine == 2 )
    {
        Pdr_Par_t Pars, * pPars = &Pars;
        Pdr_ManSetDefaultParams( pPars );
        pPars->nTimeOut = nTimeOut;
        pPars->fSilent  = 1;
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        Aig_Man_t * pAig = Gia_ManToAigSimple( p );
        Cec_CopyGiaNameToAig( p, pAig );
        RetValue = Pdr_ManSolve( pAig, pPars );
        p->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );                
    }        
    else if ( iEngine == 3 )
    {
        Saig_ParBmc_t Pars, * pPars = &Pars;
        Saig_ParBmcSetDefaultParams( pPars );
        pPars->fUseGlucose = 1;
        pPars->nTimeOut    = nTimeOut;
        pPars->fSilent     = 1;
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        Aig_Man_t * pAig = Gia_ManToAigSimple( p );
        Cec_CopyGiaNameToAig( p, pAig );
        RetValue = Saig_ManBmcScalable( pAig, pPars );
        p->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );                
    }
    else if ( iEngine == 4 )
    {
        Pdr_Par_t Pars, * pPars = &Pars;
        Pdr_ManSetDefaultParams( pPars );
        pPars->fUseAbs  = 1;
        pPars->nTimeOut = nTimeOut;
        pPars->fSilent  = 1;
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        Aig_Man_t * pAig = Gia_ManToAigSimple( p );
        Cec_CopyGiaNameToAig( p, pAig );
        RetValue = Pdr_ManSolve( pAig, pPars );
        p->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );                
    }
    else if ( iEngine == 5 )
    {
        Bmc_AndPar_t Pars, * pPars = &Pars;
        memset( pPars, 0, sizeof(Bmc_AndPar_t) );
        pPars->nProcs        =        1;  // the number of parallel solvers        
        pPars->nFramesAdd    =        1;  // the number of additional frames
        pPars->fNotVerbose   =        1;  // silent
        pPars->nTimeOut      = nTimeOut;  // timeout in seconds
        if ( pThData && pThData->pShare )
        {
            pPars->pFuncProgress = Cec_SProveCallback;
            pPars->pProgress     = (void *)pThData;
        }
        RetValue = Bmcg_ManPerform( p, pPars );
    }
    else if ( iEngine == PAR_ENGINE_UFAR )
    {
        if ( pThData && pThData->pWlc )
        {
            g_pUfarShare = pThData->pShare;
            RetValue = Ufar_ProveWithTimeout( pThData->pWlc, pThData->nTimeOutU, fVerbose, Cec_SProveStopUfar, 0 );
            g_pUfarShare = NULL;
        }
    }
    else if ( iEngine == PAR_ENGINE_GLA )
    {
        if ( Gia_ManPoNum(p) != 1 )
            return -1;
        Abs_Par_t Pars, * pPars = &Pars;
        Abs_ParSetDefaults( pPars );
        pPars->nTimeOut = nTimeOut;
        pPars->fCallProver = 1; // emulate "&gla -q"
        pPars->fVerbose = 0;
        pPars->fVeryVerbose = 0;
        pPars->RunId = 0;
        pPars->pFuncStop = Cec_SProveStopGla;
        g_pGlaShare = pThData ? pThData->pShare : NULL;
        RetValue = Gia_ManPerformGla( p, pPars );
        g_pGlaShare = NULL;
    }
    else assert( 0 );
    //while ( Abc_Clock() < clkStop );
    if ( pThData && pThData->pShare && RetValue != -1 )
        Cec_SProveCallback( (void *)pThData, 1, (unsigned)RetValue );
    if ( fVerbose ) {
        printf( "Engine %d finished and %ssolved the problem.   ", iEngine, RetValue != -1 ? "    " : "not " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return RetValue;
}
Gia_Man_t * Cec_GiaScorrOld( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare )
{
    Cec_ScorrStop_t Stop;
    Stop.pShare = pShare;
    Stop.TimeToStop = nTimeOut > 0 ? (abctime)(Abc_Clock() + (abctime)nTimeOut * CLOCKS_PER_SEC) : 0;
    if ( Gia_ManRegNum(p) == 0 )
        return Gia_ManDup( p );
    Ssw_Pars_t Pars, * pPars = &Pars;
    Ssw_ManSetDefaultParams( pPars );
    pPars->pFunc = (void *)Cec_ScorrStop;
    pPars->pData = (void *)&Stop;
    Aig_Man_t * pAig  = Gia_ManToAigSimple( p );
    Aig_Man_t * pAig2 = Ssw_SignalCorrespondence( pAig, pPars );
    Gia_Man_t * pGia2 = Gia_ManFromAigSimple( pAig2 );
    Aig_ManStop( pAig2 );  
    Aig_ManStop( pAig );
    return pGia2;     
}
Gia_Man_t * Cec_GiaScorrNew( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare )
{
    Cec_ScorrStop_t Stop;
    Stop.pShare = pShare;
    Stop.TimeToStop = nTimeOut > 0 ? (abctime)(Abc_Clock() + (abctime)nTimeOut * CLOCKS_PER_SEC) : 0;
    if ( Gia_ManRegNum(p) == 0 )
        return Gia_ManDup( p );
    Cec_ParCor_t Pars, * pPars = &Pars;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->nBTLimit   = 100;
    pPars->nLevelMax  = 100;
    pPars->fVerbose   = 0;
    pPars->fUseCSat   = 1;
    pPars->pFunc      = (void *)Cec_ScorrStop;
    pPars->pData      = (void *)&Stop;
    return Cec_ManLSCorrespondence( p, pPars ); 
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Cec_GiaProveWorkerThread( void * pArg )
{
    Par_ThData_t * pThData = (Par_ThData_t *)pArg;
    volatile int * pPlace = &pThData->fWorking;
    while ( 1 )
    {
        while ( *pPlace == 0 );
        assert( pThData->fWorking );
        if ( pThData->p == NULL )
        {
            pthread_exit( NULL );
            assert( 0 );
            return NULL;
        }
        pThData->Result = Cec_GiaProveOne( pThData->p, pThData->iEngine, pThData->nTimeOut, pThData->fVerbose, pThData );
        pThData->fWorking = 0;
    }
    assert( 0 );
    return NULL;
}
void Cec_GiaInitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int nTimeOut, int nTimeOutU, Wlc_Ntk_t * pWlc, int fUseUif, int fVerbose, pthread_t * WorkerThread, Par_Share_t * pShare )
{
    int i, status;
    assert( nWorkers <= PAR_THR_MAX );
    for ( i = 0; i < nWorkers; i++ )
    {
        ThData[i].p        = Gia_ManDup(p);
        Cec_CopyGiaName( p, ThData[i].p );
        if ( fUseUif && i == nWorkers - 1 )
            ThData[i].iEngine = PAR_ENGINE_UFAR;
        else if ( !fUseUif && nWorkers == 6 && i == 5 )
            ThData[i].iEngine = PAR_ENGINE_GLA;
        else
            ThData[i].iEngine = i;
        ThData[i].nTimeOut = nTimeOut;
        ThData[i].fWorking = 0;
        ThData[i].Result   = -1;
        ThData[i].fVerbose = fVerbose;
        ThData[i].nTimeOutU= nTimeOutU;
        ThData[i].pWlc     = pWlc;
        ThData[i].pShare   = pShare;
        if ( !WorkerThread )
            continue;
        status = pthread_create( WorkerThread + i, NULL,Cec_GiaProveWorkerThread, (void *)(ThData + i) );  assert( status == 0 );
    }
    for ( i = 0; i < nWorkers; i++ )
        ThData[i].fWorking = 1;
}
int Cec_GiaWaitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int RetValue, int * pRetEngine )
{
    int i;
    for ( i = 0; i < nWorkers; i++ )
    {
        if ( RetValue == -1 && !ThData[i].fWorking && ThData[i].Result != -1 ) {
            RetValue = ThData[i].Result;
            *pRetEngine = ThData[i].iEngine;
            if ( !p->pCexSeq && ThData[i].p->pCexSeq )
                p->pCexSeq = Abc_CexDup( ThData[i].p->pCexSeq, -1 );
        }
        if ( ThData[i].fWorking )
            i = -1;
    }
    return RetValue;
}
    
int Cec_GiaProveTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent )
{
    abctime clkScorr = 0, clkTotal = Abc_Clock();
    Par_ThData_t ThData[PAR_THR_MAX];
    pthread_t WorkerThread[PAR_THR_MAX];
    Par_Share_t Share;
    int i, nWorkers = nProcs + (fUseUif ? 1 : 0), RetValue = -1, RetEngine = -1;
    memset( &Share, 0, sizeof(Par_Share_t) );
    Abc_CexFreeP( &p->pCexComb );
    Abc_CexFreeP( &p->pCexSeq );        
    if ( !fSilent && fVerbose )
        printf( "Solving verification problem with the following parameters:\n" );
    if ( !fSilent && fVerbose )
        printf( "Processes = %d   TimeOut = %d sec   Verbose = %d.\n", nProcs, nTimeOut, fVerbose );
    fflush( stdout );

    assert( nProcs == 3 || nProcs == 5 || nProcs == 6 );
    assert( nWorkers <= PAR_THR_MAX );
    Cec_GiaInitThreads( ThData, nWorkers, p, nTimeOut, nTimeOut3, pWlc, fUseUif, fVerbose, WorkerThread, &Share );

    // meanwhile, perform scorr
    Gia_Man_t * pScorr = Cec_GiaScorrNew( p, nTimeOut, &Share );
    clkScorr = Abc_Clock() - clkTotal;
    if ( Gia_ManAndNum(pScorr) == 0 )
        RetValue = 1, RetEngine = PAR_ENGINE_SCORR1;
    
    RetValue = Cec_GiaWaitThreads( ThData, nWorkers, p, RetValue, &RetEngine );
    if ( RetValue == -1 )
    {
        abctime clkScorr2, clkStart = Abc_Clock();
        if ( !fSilent && fVerbose ) {
            printf( "Reduced the miter from %d to %d nodes. ", Gia_ManAndNum(p), Gia_ManAndNum(pScorr) );
            Abc_PrintTime( 1, "Time", clkScorr );
        }
        Cec_GiaInitThreads( ThData, nWorkers, pScorr, nTimeOut2, nTimeOut3, pWlc, fUseUif, fVerbose, NULL, &Share );

        RetValue = Cec_GiaWaitThreads( ThData, nWorkers, p, RetValue, &RetEngine );
        if ( RetValue == -1 && Gia_ManAndNum(pScorr) < 100000 )
        {
            // Run this reduction only when round-2 did not decide the problem.
            Gia_Man_t * pScorr2 = Cec_GiaScorrOld( pScorr, nTimeOut3, &Share );
            clkScorr2 = Abc_Clock() - clkStart;
            if ( Gia_ManAndNum(pScorr2) == 0 )
                RetValue = 1, RetEngine = PAR_ENGINE_SCORR2;

            if ( RetValue == -1 )
            {
                if ( !fSilent && fVerbose ) {
                    printf( "Reduced the miter from %d to %d nodes. ", Gia_ManAndNum(pScorr), Gia_ManAndNum(pScorr2) );
                    Abc_PrintTime( 1, "Time", clkScorr2 );
                }
                Cec_GiaInitThreads( ThData, nWorkers, pScorr2, nTimeOut3, nTimeOut3, pWlc, fUseUif, fVerbose, NULL, &Share );

                RetValue = Cec_GiaWaitThreads( ThData, nWorkers, p, RetValue, &RetEngine );
                // do something else      
            }
            Gia_ManStop( pScorr2 );   
        }
    }
    Gia_ManStop( pScorr );    

    // stop threads
    for ( i = 0; i < nWorkers; i++ )
    {
        ThData[i].p = NULL;
        ThData[i].fWorking = 1;
    }
    if ( !fSilent )
    {
        char * pProbName = p->pSpec ? p->pSpec : Gia_ManName(p);
        if ( RetValue != -1 && RetEngine < 0 )
            RetEngine = PAR_ENGINE_SCORR1;
        printf( "Problem \"%s\" is ", pProbName ? pProbName : "(none)" );
        if ( RetValue == 0 )
            printf( "SATISFIABLE (solved by %s).", Cec_SolveEngineName(RetEngine) );
        else if ( RetValue == 1 )
            printf( "UNSATISFIABLE (solved by %s).", Cec_SolveEngineName(RetEngine) );
        else if ( RetValue == -1 )
            printf( "UNDECIDED." );
        else assert( 0 );
        printf( "   " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkTotal );
        fflush( stdout );
    }
    return RetValue;
}

#endif // pthreads are used

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
