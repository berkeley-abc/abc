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
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
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
typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;
struct Cec_ScorrStop_t_;
struct Cec_SproveTrace_t_;
static int Cec_SProveCallback( void * pUser, int fSolved, unsigned Result );
static Gia_Man_t * Cec_GiaScorrOld( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare, struct Cec_ScorrStop_t_ * pStopOut );
static Gia_Man_t * Cec_GiaScorrNew( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare, struct Cec_ScorrStop_t_ * pStopOut );
#ifdef ABC_USE_PTHREADS
static void Cec_GiaInitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int nTimeOut, int nTimeOutU, Wlc_Ntk_t * pWlc, const char * pUfarArgs, int fVerbose, pthread_t * WorkerThread, Par_Share_t * pShare, int * pEngines, int StageId, int NetId, struct Cec_SproveTrace_t_ * pTrace );
static void Cec_GiaStopThreads( Par_ThData_t * ThData, pthread_t * WorkerThread, int nWorkers );
#endif
static int Cec_GiaWaitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int RetValue, int * pRetEngine );

extern int Ufar_ProveWithTimeout( Wlc_Ntk_t * pNtk, int nTimeOut, int fVerbose, int (*pFuncStop)(int), int RunId, const char * pArgs );

#ifndef ABC_USE_PTHREADS

int Cec_GiaProveTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent, char * pReplayFile, char * pUfarArgs ) { return -1; }
int Cec_GiaReplayReadParams( char * pFileName, int * pnProcs, int * pnTimeOut, int * pnTimeOut2, int * pnTimeOut3, int * pfUseUif ) { return 0; }
int Cec_GiaReplayTest( Gia_Man_t * p, Wlc_Ntk_t * pWlc, char * pFileName, int fVerbose, int fVeryVerbose, int fSilent ) { return -1; }

#else // pthreads are used

#define PAR_THR_MAX 8
#define PAR_ENGINE_UFAR 6
#define PAR_ENGINE_SCORR1 7
#define PAR_ENGINE_SCORR2 8
#define PAR_ENGINE_GLA 9
#define SPROVE_STAGE_MAX 4
#define SPROVE_NET_ORIG  0
#define SPROVE_NET_SCNEW 1
#define SPROVE_NET_SCOLD 2
typedef struct Cec_SproveTrace_t_ Cec_SproveTrace_t;
typedef struct Cec_SproveStage_t_ Cec_SproveStage_t;
typedef struct Cec_SprovePlan_t_ Cec_SprovePlan_t;
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
    int         fStop;
    int         nTimeOut;
    int         Result;
    int         fVerbose;
    int         nTimeOutU;
    Wlc_Ntk_t * pWlc;
    const char * pUfarArgs;
    int         WorkerId;
    int         StageId;
    int         NetId;
    int         StopReason;
    Par_Share_t * pShare;
    Cec_SproveTrace_t * pTrace;
    pthread_mutex_t Mutex;
    pthread_cond_t  Cond;
} Par_ThData_t;
typedef struct Cec_ScorrStop_t_
{
    Par_Share_t * pShare;
    abctime TimeToStop;
    int fStoppedByCallback;
    int fStoppedByTimeout;
} Cec_ScorrStop_t;
struct Cec_SproveTrace_t_
{
    FILE * pFile;
    int fActive;
    abctime clkStart;
    pthread_mutex_t Mutex;
};
struct Cec_SproveStage_t_
{
    int Id;
    int fGuardUnsolved;
    int GuardExistsNet;
    int GuardAndLimitNet;
    int GuardAndLimit;
    int fHasRound;
    int RoundNet;
    int RoundTimeout;
    int nRoundEngines;
    int RoundEngines[PAR_THR_MAX];
    int fHasReduce;
    int ReduceType;
    int ReduceNetIn;
    int ReduceNetOut;
    int ReduceTimeout;
};
struct Cec_SprovePlan_t_
{
    int nProcs;
    int nTimeOut;
    int nTimeOut2;
    int nTimeOut3;
    int fUseUif;
    int fPersistentUif;
    int nTimeOutUif;
    char * pUfarArgs;
    int nStages;
    Cec_SproveStage_t Stages[SPROVE_STAGE_MAX];
};
static volatile Par_Share_t * g_pUfarShare = NULL;
static volatile Par_Share_t * g_pGlaShare = NULL;
static inline const char * Cec_SolveEngineName( int iEngine )
{
    if ( iEngine == 0 ) return "rar";
    if ( iEngine == 1 ) return "bmc";
    if ( iEngine == 2 ) return "pdr";
    if ( iEngine == 3 ) return "bmc-g";
    if ( iEngine == 4 ) return "pdr-t";
    if ( iEngine == 5 ) return "bmcg";
    if ( iEngine == PAR_ENGINE_UFAR ) return "ufar";
    if ( iEngine == PAR_ENGINE_SCORR1 ) return "scnew";
    if ( iEngine == PAR_ENGINE_SCORR2 ) return "scold";
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
    {
        p->fStoppedByCallback = 1;
        return 1;
    }
    if ( p->TimeToStop && Abc_Clock() >= p->TimeToStop )
    {
        p->fStoppedByTimeout = 1;
        return 1;
    }
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

static inline const char * Cec_SproveNetName( int NetId )
{
    if ( NetId == SPROVE_NET_ORIG )
        return "orig";
    if ( NetId == SPROVE_NET_SCNEW )
        return "scnew";
    if ( NetId == SPROVE_NET_SCOLD )
        return "scold";
    return "unknown";
}
static inline int Cec_SproveNetId( const char * pName )
{
    if ( !strcmp(pName, "orig") )
        return SPROVE_NET_ORIG;
    if ( !strcmp(pName, "scnew") )
        return SPROVE_NET_SCNEW;
    if ( !strcmp(pName, "scold") )
        return SPROVE_NET_SCOLD;
    return -1;
}
static inline const char * Cec_SproveStopName( int StopReason )
{
    if ( StopReason == 1 )
        return "self";
    if ( StopReason == 2 )
        return "callback";
    if ( StopReason == 3 )
        return "timeout";
    if ( StopReason == 4 )
        return "skip";
    return "unknown";
}
static inline const char * Cec_SproveResultName( int RetValue )
{
    if ( RetValue == 0 )
        return "sat";
    if ( RetValue == 1 )
        return "unsat";
    return "undecided";
}
static inline unsigned long long Cec_SproveClockToMs( abctime Time )
{
    return (unsigned long long)(1000.0 * (double)Time / (double)CLOCKS_PER_SEC);
}
static int Cec_SproveFindValue( char * pLine, const char * pKey, char * pValue, int nValueSize )
{
    char * pBeg = strstr( pLine, pKey );
    int i = 0;
    if ( pBeg == NULL )
        return 0;
    pBeg += strlen(pKey);
    while ( *pBeg && *pBeg != ' ' && *pBeg != '\t' && *pBeg != '\r' && *pBeg != '\n' )
    {
        if ( i < nValueSize - 1 )
            pValue[i++] = *pBeg;
        pBeg++;
    }
    pValue[i] = 0;
    return i > 0;
}
static int Cec_SproveParseEngineName( const char * pName )
{
    int i;
    for ( i = 0; i <= PAR_ENGINE_GLA; i++ )
        if ( !strcmp(pName, Cec_SolveEngineName(i)) )
            return i;
    return -1;
}
static int Cec_SprovePlanTimeoutTotal( Cec_SprovePlan_t * pPlan )
{
    int i, Total = 0;
    for ( i = 0; i < pPlan->nStages; i++ )
    {
        Cec_SproveStage_t * pStage = &pPlan->Stages[i];
        int RoundTime = pStage->fHasRound ? pStage->RoundTimeout : 0;
        int ReduceTime = pStage->fHasReduce ? pStage->ReduceTimeout : 0;
        Total += Abc_MaxInt( RoundTime, ReduceTime );
    }
    return Total;
}
static void Cec_SproveDeriveEngineList( int nProcs, int fUseUif, int fPersistentUif, int * pEngines, int * pnEngines )
{
    int i, nEngines = nProcs + ((fUseUif && !fPersistentUif) ? 1 : 0);
    assert( nEngines >= 1 && nEngines <= PAR_THR_MAX );
    if ( fUseUif && nProcs == 6 )
    {
        if ( fPersistentUif )
        {
            int UifEngines[6] = { 0, 1, 2, 3, 4, PAR_ENGINE_GLA };
            memcpy( pEngines, UifEngines, sizeof(UifEngines) );
            *pnEngines = 6;
        }
        else
        {
            int UifEngines[7] = { 0, 1, 2, 3, 4, PAR_ENGINE_GLA, PAR_ENGINE_UFAR };
            memcpy( pEngines, UifEngines, sizeof(UifEngines) );
            *pnEngines = 7;
        }
        return;
    }
    for ( i = 0; i < nEngines; i++ )
    {
        if ( fUseUif && !fPersistentUif && i == nEngines - 1 )
            pEngines[i] = PAR_ENGINE_UFAR;
        else if ( !fUseUif && nEngines == 6 && i == 5 )
            pEngines[i] = PAR_ENGINE_GLA;
        else
            pEngines[i] = i;
    }
    *pnEngines = nEngines;
}
static void Cec_SproveTrimLineEnd( char * pLine )
{
    int nSize = strlen( pLine );
    while ( nSize > 0 && (pLine[nSize - 1] == '\n' || pLine[nSize - 1] == '\r') )
        pLine[--nSize] = 0;
}
static void Cec_SprovePlanSetUfarArgs( Cec_SprovePlan_t * pPlan, const char * pUfarArgs )
{
    ABC_FREE( pPlan->pUfarArgs );
    pPlan->pUfarArgs = NULL;
    if ( pUfarArgs && pUfarArgs[0] )
        pPlan->pUfarArgs = Abc_UtilStrsav( (char *)pUfarArgs );
}
static void Cec_SprovePlanFree( Cec_SprovePlan_t * pPlan )
{
    ABC_FREE( pPlan->pUfarArgs );
    pPlan->pUfarArgs = NULL;
}
static void Cec_SprovePlanDefault( Cec_SprovePlan_t * pPlan, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, const char * pUfarArgs )
{
    int nEngines;
    memset( pPlan, 0, sizeof(Cec_SprovePlan_t) );
    {
        int i;
        for ( i = 0; i < SPROVE_STAGE_MAX; i++ )
            pPlan->Stages[i].GuardExistsNet = pPlan->Stages[i].GuardAndLimitNet = -1;
    }
    pPlan->nProcs = nProcs;
    pPlan->nTimeOut = nTimeOut;
    pPlan->nTimeOut2 = nTimeOut2;
    pPlan->nTimeOut3 = nTimeOut3;
    pPlan->fUseUif = fUseUif;
    pPlan->fPersistentUif = fUseUif ? 1 : 0;
    Cec_SprovePlanSetUfarArgs( pPlan, pUfarArgs );
    pPlan->nStages = 4;
    Cec_SproveDeriveEngineList( nProcs, fUseUif, pPlan->fPersistentUif, pPlan->Stages[0].RoundEngines, &nEngines );

    pPlan->Stages[0].Id = 1;
    pPlan->Stages[0].fHasRound = 1;
    pPlan->Stages[0].RoundNet = SPROVE_NET_ORIG;
    pPlan->Stages[0].RoundTimeout = nTimeOut;
    pPlan->Stages[0].nRoundEngines = nEngines;
    pPlan->Stages[0].fHasReduce = 1;
    pPlan->Stages[0].ReduceType = PAR_ENGINE_SCORR1;
    pPlan->Stages[0].ReduceNetIn = SPROVE_NET_ORIG;
    pPlan->Stages[0].ReduceNetOut = SPROVE_NET_SCNEW;
    pPlan->Stages[0].ReduceTimeout = nTimeOut;

    pPlan->Stages[1].Id = 2;
    pPlan->Stages[1].fGuardUnsolved = 1;
    pPlan->Stages[1].fHasRound = 1;
    pPlan->Stages[1].RoundNet = SPROVE_NET_SCNEW;
    pPlan->Stages[1].RoundTimeout = nTimeOut2;
    pPlan->Stages[1].nRoundEngines = nEngines;
    memcpy( pPlan->Stages[1].RoundEngines, pPlan->Stages[0].RoundEngines, sizeof(int) * nEngines );

    pPlan->Stages[2].Id = 3;
    pPlan->Stages[2].fGuardUnsolved = 1;
    pPlan->Stages[2].GuardAndLimitNet = SPROVE_NET_SCNEW;
    pPlan->Stages[2].GuardAndLimit = 100000;
    pPlan->Stages[2].fHasReduce = 1;
    pPlan->Stages[2].ReduceType = PAR_ENGINE_SCORR2;
    pPlan->Stages[2].ReduceNetIn = SPROVE_NET_SCNEW;
    pPlan->Stages[2].ReduceNetOut = SPROVE_NET_SCOLD;
    pPlan->Stages[2].ReduceTimeout = nTimeOut3;

    pPlan->Stages[3].Id = 4;
    pPlan->Stages[3].fGuardUnsolved = 1;
    pPlan->Stages[3].GuardExistsNet = SPROVE_NET_SCOLD;
    pPlan->Stages[3].fHasRound = 1;
    pPlan->Stages[3].RoundNet = SPROVE_NET_SCOLD;
    pPlan->Stages[3].RoundTimeout = nTimeOut3;
    pPlan->Stages[3].nRoundEngines = nEngines;
    memcpy( pPlan->Stages[3].RoundEngines, pPlan->Stages[0].RoundEngines, sizeof(int) * nEngines );
    pPlan->nTimeOutUif = pPlan->fPersistentUif ? Cec_SprovePlanTimeoutTotal( pPlan ) : 0;
}
static void Cec_SproveTraceWrite( Cec_SproveTrace_t * pTrace, const char * pFormat, ... )
{
    va_list args;
    if ( pTrace == NULL || !pTrace->fActive || pTrace->pFile == NULL )
        return;
    pthread_mutex_lock( &pTrace->Mutex );
    va_start( args, pFormat );
    vfprintf( pTrace->pFile, pFormat, args );
    va_end( args );
    fputc( '\n', pTrace->pFile );
    fflush( pTrace->pFile );
    pthread_mutex_unlock( &pTrace->Mutex );
}
static abctime Cec_SproveTraceTime( Cec_SproveTrace_t * pTrace )
{
    return pTrace ? Abc_Clock() - pTrace->clkStart : 0;
}
static void Cec_SproveTraceOpen( Cec_SproveTrace_t * pTrace, Gia_Man_t * p, Cec_SprovePlan_t * pPlan, char * pReplayFile )
{
    int i, k;
    char * pProbName = p->pSpec ? p->pSpec : Gia_ManName(p);
    memset( pTrace, 0, sizeof(Cec_SproveTrace_t) );
    if ( pReplayFile == NULL )
        return;
    pTrace->pFile = fopen( pReplayFile, "wb" );
    if ( pTrace->pFile == NULL )
        return;
    pTrace->fActive = 1;
    pTrace->clkStart = Abc_Clock();
    pthread_mutex_init( &pTrace->Mutex, NULL );
    Cec_SproveTraceWrite( pTrace, "SPROVE_REPLAY 1" );
    Cec_SproveTraceWrite( pTrace, "CASE %s", pProbName ? pProbName : "(none)" );
    Cec_SproveTraceWrite( pTrace, "PARAMS P=%d T=%d U=%d W=%d UIF=%d", pPlan->nProcs, pPlan->nTimeOut, pPlan->nTimeOut2, pPlan->nTimeOut3, pPlan->fUseUif );
    if ( pPlan->fUseUif )
        Cec_SproveTraceWrite( pTrace, "UFAR mode=%s timeout=%d", pPlan->fPersistentUif ? "persistent" : "round", pPlan->nTimeOutUif );
    if ( pPlan->pUfarArgs && pPlan->pUfarArgs[0] )
        Cec_SproveTraceWrite( pTrace, "UFAR_ARGS %s", pPlan->pUfarArgs );
    Cec_SproveTraceWrite( pTrace, "" );
    Cec_SproveTraceWrite( pTrace, "PLAN_BEGIN" );
    for ( i = 0; i < pPlan->nStages; i++ )
    {
        Cec_SproveStage_t * pStage = &pPlan->Stages[i];
        char Buffer[256];
        Buffer[0] = 0;
        if ( pStage->fGuardUnsolved )
            strcat( Buffer, "unsolved" );
        if ( pStage->GuardExistsNet >= 0 )
            sprintf( Buffer + strlen(Buffer), "%sexists(%s)", Buffer[0] ? "," : "", Cec_SproveNetName(pStage->GuardExistsNet) );
        if ( pStage->GuardAndLimitNet >= 0 )
            sprintf( Buffer + strlen(Buffer), "%sand_lt(%s,%d)", Buffer[0] ? "," : "", Cec_SproveNetName(pStage->GuardAndLimitNet), pStage->GuardAndLimit );
        if ( !Buffer[0] )
            strcpy( Buffer, "none" );
        if ( pStage->fHasRound )
        {
            char EngBuf[128];
            EngBuf[0] = 0;
            for ( k = 0; k < pStage->nRoundEngines; k++ )
            {
                if ( k > 0 )
                    strcat( EngBuf, "," );
                strcat( EngBuf, Cec_SolveEngineName(pStage->RoundEngines[k]) );
            }
            Cec_SproveTraceWrite( pTrace, "ROUND stage=%d guard=%s net=%s timeout=%d engines=%s", pStage->Id, Buffer, Cec_SproveNetName(pStage->RoundNet), pStage->RoundTimeout, EngBuf );
        }
        if ( pStage->fHasReduce )
            Cec_SproveTraceWrite( pTrace, "REDUCE stage=%d guard=%s name=%s in=%s out=%s timeout=%d stop=callback_or_timeout", pStage->Id, Buffer, Cec_SolveEngineName(pStage->ReduceType), Cec_SproveNetName(pStage->ReduceNetIn), Cec_SproveNetName(pStage->ReduceNetOut), pStage->ReduceTimeout );
    }
    Cec_SproveTraceWrite( pTrace, "PLAN_END" );
    Cec_SproveTraceWrite( pTrace, "" );
    Cec_SproveTraceWrite( pTrace, "OBSERVED_BEGIN" );
    Cec_SproveTraceWrite( pTrace, "CHECKPOINT net=orig regs=%d ands=%d pos=%d", Gia_ManRegNum(p), Gia_ManAndNum(p), Gia_ManPoNum(p) );
}
static void Cec_SproveTraceClose( Cec_SproveTrace_t * pTrace )
{
    if ( pTrace == NULL || !pTrace->fActive )
        return;
    Cec_SproveTraceWrite( pTrace, "OBSERVED_END" );
    pthread_mutex_destroy( &pTrace->Mutex );
    fclose( pTrace->pFile );
    pTrace->pFile = NULL;
    pTrace->fActive = 0;
}
static int Cec_SproveReplayReadParamsInt( char * pFileName, Cec_SprovePlan_t * pPlan )
{
    char Buffer[1024], Value[256];
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
        return 0;
    memset( pPlan, 0, sizeof(Cec_SprovePlan_t) );
    {
        int i;
        for ( i = 0; i < SPROVE_STAGE_MAX; i++ )
            pPlan->Stages[i].GuardExistsNet = pPlan->Stages[i].GuardAndLimitNet = -1;
    }
    while ( fgets( Buffer, sizeof(Buffer), pFile ) != NULL )
    {
        if ( strncmp(Buffer, "PARAMS ", 7) == 0 )
        {
            if ( !Cec_SproveFindValue(Buffer, "P=", Value, sizeof(Value)) ) break;
            pPlan->nProcs = atoi(Value);
            if ( !Cec_SproveFindValue(Buffer, "T=", Value, sizeof(Value)) ) break;
            pPlan->nTimeOut = atoi(Value);
            if ( !Cec_SproveFindValue(Buffer, "U=", Value, sizeof(Value)) ) break;
            pPlan->nTimeOut2 = atoi(Value);
            if ( !Cec_SproveFindValue(Buffer, "W=", Value, sizeof(Value)) ) break;
            pPlan->nTimeOut3 = atoi(Value);
            if ( !Cec_SproveFindValue(Buffer, "UIF=", Value, sizeof(Value)) ) break;
            pPlan->fUseUif = atoi(Value);
        }
        else if ( strncmp(Buffer, "UFAR_ARGS ", 10) == 0 )
        {
            Cec_SproveTrimLineEnd( Buffer );
            Cec_SprovePlanSetUfarArgs( pPlan, Buffer + 10 );
        }
        else if ( strncmp(Buffer, "UFAR ", 5) == 0 )
        {
            if ( Cec_SproveFindValue(Buffer, "mode=", Value, sizeof(Value)) )
                pPlan->fPersistentUif = !strcmp(Value, "persistent");
            if ( Cec_SproveFindValue(Buffer, "timeout=", Value, sizeof(Value)) )
                pPlan->nTimeOutUif = atoi(Value);
        }
        else if ( pPlan->nProcs > 0 && (strncmp(Buffer, "PLAN_BEGIN", 10) == 0 || strncmp(Buffer, "OBSERVED_BEGIN", 14) == 0) )
        {
            if ( pPlan->fUseUif && pPlan->nTimeOutUif == 0 )
                pPlan->nTimeOutUif = pPlan->fPersistentUif ? (pPlan->nTimeOut + pPlan->nTimeOut2 + 2 * pPlan->nTimeOut3) : 0;
            fclose( pFile );
            return 1;
        }
    }
    fclose( pFile );
    return pPlan->nProcs > 0;
}
static int Cec_SproveReplayReadPlan( char * pFileName, Cec_SprovePlan_t * pPlan )
{
    char Buffer[1024], Value[256], Guard[256], Engines[256];
    FILE * pFile;
    int fInPlan = 0;
    if ( !Cec_SproveReplayReadParamsInt( pFileName, pPlan ) )
        return 0;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
        return 0;
    while ( fgets( Buffer, sizeof(Buffer), pFile ) != NULL )
    {
        Cec_SproveStage_t * pStage;
        int StageId;
        if ( strncmp(Buffer, "PLAN_BEGIN", 10) == 0 )
        {
            fInPlan = 1;
            continue;
        }
        if ( strncmp(Buffer, "PLAN_END", 8) == 0 || strncmp(Buffer, "OBSERVED_BEGIN", 14) == 0 )
            break;
        if ( !fInPlan )
            continue;
        if ( strncmp(Buffer, "ROUND ", 6) == 0 )
        {
            char * pTok;
            int nEngines = 0;
            if ( !Cec_SproveFindValue(Buffer, "stage=", Value, sizeof(Value)) )
                continue;
            StageId = atoi(Value);
            if ( StageId < 1 || StageId > SPROVE_STAGE_MAX )
                continue;
            pStage = &pPlan->Stages[StageId - 1];
            if ( StageId > pPlan->nStages )
                pPlan->nStages = StageId;
            memset( Guard, 0, sizeof(Guard) );
            Cec_SproveFindValue(Buffer, "guard=", Guard, sizeof(Guard));
            pStage->Id = StageId;
            pStage->fGuardUnsolved = strstr( Guard, "unsolved" ) != NULL;
            if ( strstr(Guard, "exists(") )
            {
                sscanf( strstr(Guard, "exists("), "exists(%255[^)])", Value );
                pStage->GuardExistsNet = Cec_SproveNetId( Value );
            }
            if ( strstr(Guard, "and_lt(") )
            {
                sscanf( strstr(Guard, "and_lt("), "and_lt(%255[^,],%d)", Value, &pStage->GuardAndLimit );
                pStage->GuardAndLimitNet = Cec_SproveNetId( Value );
            }
            if ( Cec_SproveFindValue(Buffer, "net=", Value, sizeof(Value)) )
                pStage->RoundNet = Cec_SproveNetId( Value );
            if ( Cec_SproveFindValue(Buffer, "timeout=", Value, sizeof(Value)) )
                pStage->RoundTimeout = atoi(Value);
            if ( Cec_SproveFindValue(Buffer, "engines=", Engines, sizeof(Engines)) )
            {
                pTok = strtok( Engines, "," );
                while ( pTok && nEngines < PAR_THR_MAX )
                {
                    pStage->RoundEngines[nEngines++] = Cec_SproveParseEngineName( pTok );
                    pTok = strtok( NULL, "," );
                }
            }
            pStage->fHasRound = 1;
            pStage->nRoundEngines = nEngines;
        }
        else if ( strncmp(Buffer, "REDUCE ", 7) == 0 )
        {
            if ( !Cec_SproveFindValue(Buffer, "stage=", Value, sizeof(Value)) )
                continue;
            StageId = atoi(Value);
            if ( StageId < 1 || StageId > SPROVE_STAGE_MAX )
                continue;
            pStage = &pPlan->Stages[StageId - 1];
            if ( StageId > pPlan->nStages )
                pPlan->nStages = StageId;
            memset( Guard, 0, sizeof(Guard) );
            Cec_SproveFindValue(Buffer, "guard=", Guard, sizeof(Guard));
            pStage->Id = StageId;
            pStage->fGuardUnsolved = strstr( Guard, "unsolved" ) != NULL;
            if ( strstr(Guard, "exists(") )
            {
                sscanf( strstr(Guard, "exists("), "exists(%255[^)])", Value );
                pStage->GuardExistsNet = Cec_SproveNetId( Value );
            }
            if ( strstr(Guard, "and_lt(") )
            {
                sscanf( strstr(Guard, "and_lt("), "and_lt(%255[^,],%d)", Value, &pStage->GuardAndLimit );
                pStage->GuardAndLimitNet = Cec_SproveNetId( Value );
            }
            if ( Cec_SproveFindValue(Buffer, "name=", Value, sizeof(Value)) )
                pStage->ReduceType = Cec_SproveParseEngineName( Value );
            if ( Cec_SproveFindValue(Buffer, "in=", Value, sizeof(Value)) )
                pStage->ReduceNetIn = Cec_SproveNetId( Value );
            if ( Cec_SproveFindValue(Buffer, "out=", Value, sizeof(Value)) )
                pStage->ReduceNetOut = Cec_SproveNetId( Value );
            if ( Cec_SproveFindValue(Buffer, "timeout=", Value, sizeof(Value)) )
                pStage->ReduceTimeout = atoi(Value);
            pStage->fHasReduce = 1;
        }
    }
    fclose( pFile );
    return pPlan->nStages > 0;
}
static Gia_Man_t * Cec_SproveGetNet( int NetId, Gia_Man_t * pOrig, Gia_Man_t * pScorr, Gia_Man_t * pScorr2 )
{
    if ( NetId == SPROVE_NET_ORIG )
        return pOrig;
    if ( NetId == SPROVE_NET_SCNEW )
        return pScorr;
    if ( NetId == SPROVE_NET_SCOLD )
        return pScorr2;
    return NULL;
}
static void Cec_SproveSetNet( int NetId, Gia_Man_t ** ppScorr, Gia_Man_t ** ppScorr2, Gia_Man_t * pNet )
{
    if ( NetId == SPROVE_NET_SCNEW )
    {
        Gia_ManStopP( ppScorr );
        *ppScorr = pNet;
    }
    else if ( NetId == SPROVE_NET_SCOLD )
    {
        Gia_ManStopP( ppScorr2 );
        *ppScorr2 = pNet;
    }
    else
        Gia_ManStop( pNet );
}
static int Cec_SproveCheckGuard( Cec_SproveStage_t * pStage, int RetValue, Gia_Man_t * pOrig, Gia_Man_t * pScorr, Gia_Man_t * pScorr2 )
{
    Gia_Man_t * pNet;
    if ( pStage->fGuardUnsolved && RetValue != -1 )
        return 0;
    if ( pStage->GuardExistsNet >= 0 && Cec_SproveGetNet( pStage->GuardExistsNet, pOrig, pScorr, pScorr2 ) == NULL )
        return 0;
    if ( pStage->GuardAndLimitNet >= 0 )
    {
        pNet = Cec_SproveGetNet( pStage->GuardAndLimitNet, pOrig, pScorr, pScorr2 );
        if ( pNet == NULL || Gia_ManAndNum(pNet) >= pStage->GuardAndLimit )
            return 0;
    }
    return 1;
}
static void Cec_SproveTraceCheckpoint( Cec_SproveTrace_t * pTrace, int NetId, Gia_Man_t * pNet )
{
    if ( pTrace == NULL || !pTrace->fActive || pNet == NULL )
        return;
    Cec_SproveTraceWrite( pTrace, "CHECKPOINT net=%s regs=%d ands=%d pos=%d", Cec_SproveNetName(NetId), Gia_ManRegNum(pNet), Gia_ManAndNum(pNet), Gia_ManPoNum(pNet) );
}
static Gia_Man_t * Cec_SproveRunReduce( Gia_Man_t * pInput, Cec_SproveStage_t * pStage, Par_Share_t * pShare, Cec_SproveTrace_t * pTrace, abctime * pClkUsed, int * pRetValue, int * pRetEngine )
{
    Cec_ScorrStop_t Stop;
    abctime clk = Abc_Clock();
    Gia_Man_t * pOutput = NULL;
    int StopReason = 1;
    memset( &Stop, 0, sizeof(Stop) );
    if ( pTrace && pTrace->fActive )
        Cec_SproveTraceWrite( pTrace, "START kind=reduce stage=%d name=%s in=%s out=%s timeout=%d t=%llu",
            pStage->Id, Cec_SolveEngineName(pStage->ReduceType), Cec_SproveNetName(pStage->ReduceNetIn), Cec_SproveNetName(pStage->ReduceNetOut), pStage->ReduceTimeout,
            Cec_SproveClockToMs( Cec_SproveTraceTime(pTrace) ) );
    if ( pStage->ReduceType == PAR_ENGINE_SCORR1 )
        pOutput = Cec_GiaScorrNew( pInput, pStage->ReduceTimeout, pShare, &Stop );
    else if ( pStage->ReduceType == PAR_ENGINE_SCORR2 )
        pOutput = Cec_GiaScorrOld( pInput, pStage->ReduceTimeout, pShare, &Stop );
    else
        assert( 0 );
    if ( Gia_ManAndNum(pOutput) == 0 )
    {
        pShare->fSolved = 1;
        pShare->Result  = 1;
        pShare->iEngine = pStage->ReduceType;
        *pRetValue = 1;
        *pRetEngine = pStage->ReduceType;
    }
    if ( Stop.fStoppedByCallback )
        StopReason = 2;
    else if ( Stop.fStoppedByTimeout )
        StopReason = 3;
    if ( pClkUsed )
        *pClkUsed = Abc_Clock() - clk;
    if ( pTrace && pTrace->fActive )
    {
        Cec_SproveTraceWrite( pTrace, "STOP kind=reduce stage=%d name=%s in=%s out=%s result=%s stop=%s t=%llu elapsed=%llu",
            pStage->Id, Cec_SolveEngineName(pStage->ReduceType), Cec_SproveNetName(pStage->ReduceNetIn), Cec_SproveNetName(pStage->ReduceNetOut),
            *pRetEngine == pStage->ReduceType ? Cec_SproveResultName(*pRetValue) : "undecided",
            Cec_SproveStopName(StopReason), Cec_SproveClockToMs( Cec_SproveTraceTime(pTrace) ), Cec_SproveClockToMs( Abc_Clock() - clk ) );
        Cec_SproveTraceCheckpoint( pTrace, pStage->ReduceNetOut, pOutput );
    }
    return pOutput;
}
static void Cec_SproveTakeSharedResult( Par_Share_t * pShare, int * pRetValue, int * pRetEngine )
{
    if ( pShare == NULL || pRetValue == NULL || pRetEngine == NULL )
        return;
    if ( *pRetValue == -1 && pShare->fSolved )
    {
        *pRetValue = (int)pShare->Result;
        *pRetEngine = pShare->iEngine;
    }
}
static int Cec_SproveExecutePlan( Gia_Man_t * p, Cec_SprovePlan_t * pPlan, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent, char * pReplayFile )
{
    abctime clkTotal = Abc_Clock(), clkStage = 0;
    Par_ThData_t ThData[PAR_THR_MAX];
    pthread_t WorkerThread[PAR_THR_MAX];
    Par_ThData_t UifData[1];
    pthread_t UifThread[1];
    Par_Share_t Share;
    Cec_SproveTrace_t Trace;
    Gia_Man_t * pScorr = NULL, * pScorr2 = NULL;
    int UifEngines[1] = { PAR_ENGINE_UFAR };
    int i, RetValue = -1, RetEngine = -1, fThreadsStarted = 0, fUifStarted = 0;
    (void)fVeryVerbose;
    memset( &Share, 0, sizeof(Par_Share_t) );
    memset( &Trace, 0, sizeof(Cec_SproveTrace_t) );
    memset( ThData, 0, sizeof(ThData) );
    memset( WorkerThread, 0, sizeof(WorkerThread) );
    memset( UifData, 0, sizeof(UifData) );
    memset( UifThread, 0, sizeof(UifThread) );
    Abc_CexFreeP( &p->pCexComb );
    Abc_CexFreeP( &p->pCexSeq );
    if ( !fSilent && fVerbose )
        printf( "Solving verification problem with the following parameters:\n" );
    if ( !fSilent && fVerbose )
        printf( "Processes = %d   TimeOut = %d sec   Verbose = %d.\n", pPlan->nProcs, pPlan->nTimeOut, fVerbose );
    fflush( stdout );
    Cec_SproveTraceOpen( &Trace, p, pPlan, pReplayFile );
    if ( pPlan->fUseUif && pPlan->fPersistentUif && pWlc != NULL )
    {
        Cec_SproveTraceWrite( &Trace, "START kind=ufar mode=persistent timeout=%d t=%llu",
            pPlan->nTimeOutUif, Cec_SproveClockToMs( Cec_SproveTraceTime(&Trace) ) );
        Cec_GiaInitThreads( UifData, 1, p, pPlan->nTimeOutUif, pPlan->nTimeOutUif, pWlc, pPlan->pUfarArgs, fVerbose,
            UifThread, &Share, UifEngines, 0, SPROVE_NET_ORIG, &Trace );
        fUifStarted = 1;
    }
    for ( i = 0; i < pPlan->nStages; i++ )
    {
        Cec_SproveStage_t * pStage = &pPlan->Stages[i];
        Gia_Man_t * pRoundNet = NULL, * pReduceNet = NULL, * pReduceOut = NULL;
        Cec_SproveTakeSharedResult( &Share, &RetValue, &RetEngine );
        if ( !Cec_SproveCheckGuard( pStage, RetValue, p, pScorr, pScorr2 ) )
        {
            Cec_SproveTraceWrite( &Trace, "SKIP stage=%d reason=guard", pStage->Id );
            continue;
        }
        if ( pStage->fHasRound )
        {
            pRoundNet = Cec_SproveGetNet( pStage->RoundNet, p, pScorr, pScorr2 );
            if ( pRoundNet == NULL )
            {
                Cec_SproveTraceWrite( &Trace, "SKIP stage=%d reason=missing_round_net", pStage->Id );
                continue;
            }
            Cec_SproveTraceWrite( &Trace, "START kind=round stage=%d net=%s timeout=%d t=%llu",
                pStage->Id, Cec_SproveNetName(pStage->RoundNet), pStage->RoundTimeout, Cec_SproveClockToMs( Cec_SproveTraceTime(&Trace) ) );
            Cec_GiaInitThreads( ThData, pStage->nRoundEngines, pRoundNet, pStage->RoundTimeout, pStage->RoundTimeout, pWlc, pPlan->pUfarArgs, fVerbose,
                fThreadsStarted ? NULL : WorkerThread, &Share, pStage->RoundEngines, pStage->Id, pStage->RoundNet, &Trace );
            fThreadsStarted = 1;
        }
        if ( pStage->fHasReduce )
        {
            pReduceNet = Cec_SproveGetNet( pStage->ReduceNetIn, p, pScorr, pScorr2 );
            if ( pReduceNet == NULL )
                Cec_SproveTraceWrite( &Trace, "SKIP stage=%d reason=missing_reduce_net", pStage->Id );
            else
            {
                pReduceOut = Cec_SproveRunReduce( pReduceNet, pStage, &Share, &Trace, &clkStage, &RetValue, &RetEngine );
                Cec_SproveSetNet( pStage->ReduceNetOut, &pScorr, &pScorr2, pReduceOut );
                Cec_SproveTakeSharedResult( &Share, &RetValue, &RetEngine );
            }
        }
        if ( pStage->fHasRound )
        {
            RetValue = Cec_GiaWaitThreads( ThData, pStage->nRoundEngines, p, RetValue, &RetEngine );
            Cec_SproveTakeSharedResult( &Share, &RetValue, &RetEngine );
            Cec_SproveTraceWrite( &Trace, "STOP kind=round stage=%d net=%s result=%s winner=%s t=%llu",
                pStage->Id, Cec_SproveNetName(pStage->RoundNet), Cec_SproveResultName(RetValue),
                RetEngine >= 0 ? Cec_SolveEngineName(RetEngine) : "none", Cec_SproveClockToMs( Cec_SproveTraceTime(&Trace) ) );
        }
        if ( pStage->fHasReduce && RetValue == -1 && !fSilent && fVerbose )
        {
            Gia_Man_t * pAfter = Cec_SproveGetNet( pStage->ReduceNetOut, p, pScorr, pScorr2 );
            if ( pAfter )
            {
                printf( "Reduced the miter from %d to %d nodes. ",
                    Gia_ManAndNum(Cec_SproveGetNet(pStage->ReduceNetIn, p, pScorr, pScorr2)), Gia_ManAndNum(pAfter) );
                Abc_PrintTime( 1, "Time", clkStage );
            }
        }
    }
    if ( fUifStarted )
    {
        RetValue = Cec_GiaWaitThreads( UifData, 1, p, RetValue, &RetEngine );
        Cec_SproveTakeSharedResult( &Share, &RetValue, &RetEngine );
        Cec_SproveTraceWrite( &Trace, "STOP kind=ufar mode=persistent result=%s winner=%s t=%llu",
            Cec_SproveResultName(RetValue), RetEngine == PAR_ENGINE_UFAR ? "ufar" : "other",
            Cec_SproveClockToMs( Cec_SproveTraceTime(&Trace) ) );
    }
    if ( fThreadsStarted )
        Cec_GiaStopThreads( ThData, WorkerThread, pPlan->Stages[0].nRoundEngines );
    if ( fUifStarted )
        Cec_GiaStopThreads( UifData, UifThread, 1 );
    Gia_ManStopP( &pScorr2 );
    Gia_ManStopP( &pScorr );
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
    Cec_SproveTraceWrite( &Trace, "FINAL result=%s winner=%s total=%llu",
        Cec_SproveResultName(RetValue), RetEngine >= 0 ? Cec_SolveEngineName(RetEngine) : "none",
        Cec_SproveClockToMs( Abc_Clock() - clkTotal ) );
    Cec_SproveTraceClose( &Trace );
    return RetValue;
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
    if ( pThData && pThData->pTrace )
        Cec_SproveTraceWrite( pThData->pTrace, "START kind=engine stage=%d net=%s engine=%s worker=%d timeout=%d t=%llu",
            pThData->StageId, Cec_SproveNetName(pThData->NetId), Cec_SolveEngineName(iEngine), pThData->WorkerId, nTimeOut,
            Cec_SproveClockToMs( Cec_SproveTraceTime(pThData->pTrace) ) );
    if ( iEngine != PAR_ENGINE_UFAR && iEngine != PAR_ENGINE_GLA && Gia_ManRegNum(p) == 0 )
    {
        if ( fVerbose )
            printf( "Engine %d (%-5s) skipped because the current miter is combinational.\n", iEngine, Cec_SolveEngineName(iEngine) );
        if ( pThData && pThData->pTrace )
            Cec_SproveTraceWrite( pThData->pTrace, "STOP kind=engine stage=%d net=%s engine=%s worker=%d result=undecided stop=skip t=%llu",
                pThData->StageId, Cec_SproveNetName(pThData->NetId), Cec_SolveEngineName(iEngine), pThData->WorkerId,
                Cec_SproveClockToMs( Cec_SproveTraceTime(pThData->pTrace) ) );
        return -1;
    }
    //abctime clkStop = nTimeOut * CLOCKS_PER_SEC + Abc_Clock();
    if ( fVerbose )
    printf( "Calling engine %d (%-5s) with timeout %d sec.\n", iEngine, Cec_SolveEngineName(iEngine), nTimeOut );
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
            RetValue = Ufar_ProveWithTimeout( pThData->pWlc, pThData->nTimeOutU, fVerbose, Cec_SProveStopUfar, 0, pThData->pUfarArgs );
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
    if ( pThData )
    {
        if ( RetValue != -1 )
            pThData->StopReason = 1;
        else if ( pThData->pShare && pThData->pShare->fSolved )
            pThData->StopReason = 2;
        else
            pThData->StopReason = 3;
    }
    if ( pThData && pThData->pTrace )
        Cec_SproveTraceWrite( pThData->pTrace, "STOP kind=engine stage=%d net=%s engine=%s worker=%d result=%s stop=%s t=%llu elapsed=%llu",
            pThData->StageId, Cec_SproveNetName(pThData->NetId), Cec_SolveEngineName(iEngine), pThData->WorkerId,
            Cec_SproveResultName(RetValue), Cec_SproveStopName(pThData->StopReason),
            Cec_SproveClockToMs( Cec_SproveTraceTime(pThData->pTrace) ),
            Cec_SproveClockToMs( Abc_Clock() - clk ) );
    if ( fVerbose ) {
        printf( "Engine %d (%-5s) finished and %ssolved the problem.   ", iEngine, Cec_SolveEngineName(iEngine), RetValue != -1 ? "    " : "not " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return RetValue;
}
Gia_Man_t * Cec_GiaScorrOld( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare, Cec_ScorrStop_t * pStopOut )
{
    Cec_ScorrStop_t Stop;
    memset( &Stop, 0, sizeof(Stop) );
    Stop.pShare = pShare;
    Stop.TimeToStop = nTimeOut > 0 ? (abctime)(Abc_Clock() + (abctime)nTimeOut * CLOCKS_PER_SEC) : 0;
    if ( Gia_ManRegNum(p) == 0 )
    {
        if ( pStopOut )
            *pStopOut = Stop;
        return Gia_ManDup( p );
    }
    Ssw_Pars_t Pars, * pPars = &Pars;
    Ssw_ManSetDefaultParams( pPars );
    pPars->pFunc = (void *)Cec_ScorrStop;
    pPars->pData = (void *)&Stop;
    Aig_Man_t * pAig  = Gia_ManToAigSimple( p );
    Aig_Man_t * pAig2 = Ssw_SignalCorrespondence( pAig, pPars );
    Gia_Man_t * pGia2 = Gia_ManFromAigSimple( pAig2 );
    Aig_ManStop( pAig2 );  
    Aig_ManStop( pAig );
    if ( pStopOut )
        *pStopOut = Stop;
    return pGia2;     
}
Gia_Man_t * Cec_GiaScorrNew( Gia_Man_t * p, int nTimeOut, Par_Share_t * pShare, Cec_ScorrStop_t * pStopOut )
{
    Cec_ScorrStop_t Stop;
    memset( &Stop, 0, sizeof(Stop) );
    Stop.pShare = pShare;
    Stop.TimeToStop = nTimeOut > 0 ? (abctime)(Abc_Clock() + (abctime)nTimeOut * CLOCKS_PER_SEC) : 0;
    if ( Gia_ManRegNum(p) == 0 )
    {
        if ( pStopOut )
            *pStopOut = Stop;
        return Gia_ManDup( p );
    }
    Cec_ParCor_t Pars, * pPars = &Pars;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->nBTLimit   = 100;
    pPars->nLevelMax  = 100;
    pPars->fVerbose   = 0;
    pPars->fUseCSat   = 1;
    pPars->pFunc      = (void *)Cec_ScorrStop;
    pPars->pData      = (void *)&Stop;
    p = Cec_ManLSCorrespondence( p, pPars );
    if ( pStopOut )
        *pStopOut = Stop;
    return p;
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
    int status, Result;
    status = pthread_mutex_lock( &pThData->Mutex );
    assert( status == 0 );
    while ( 1 )
    {
        while ( !pThData->fWorking && !pThData->fStop )
        {
            status = pthread_cond_wait( &pThData->Cond, &pThData->Mutex );
            assert( status == 0 );
        }
        if ( pThData->fStop )
            break;
        status = pthread_mutex_unlock( &pThData->Mutex );
        assert( status == 0 );
        Result = Cec_GiaProveOne( pThData->p, pThData->iEngine, pThData->nTimeOut, pThData->fVerbose, pThData );
        status = pthread_mutex_lock( &pThData->Mutex );
        assert( status == 0 );
        pThData->Result = Result;
        pThData->fWorking = 0;
        status = pthread_cond_broadcast( &pThData->Cond );
        assert( status == 0 );
    }
    status = pthread_mutex_unlock( &pThData->Mutex );
    assert( status == 0 );
    return NULL;
}
static void Cec_GiaStartThreads( Par_ThData_t * ThData, int nWorkers )
{
    int i, status;
    for ( i = 0; i < nWorkers; i++ )
    {
        status = pthread_mutex_lock( &ThData[i].Mutex );
        assert( status == 0 );
        assert( !ThData[i].fStop );
        assert( !ThData[i].fWorking );
        ThData[i].fWorking = 1;
        status = pthread_cond_signal( &ThData[i].Cond );
        assert( status == 0 );
        status = pthread_mutex_unlock( &ThData[i].Mutex );
        assert( status == 0 );
    }
}
static void Cec_GiaInitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int nTimeOut, int nTimeOutU, Wlc_Ntk_t * pWlc, const char * pUfarArgs, int fVerbose, pthread_t * WorkerThread, Par_Share_t * pShare, int * pEngines, int StageId, int NetId, Cec_SproveTrace_t * pTrace )
{
    int i, status;
    assert( nWorkers <= PAR_THR_MAX );
    for ( i = 0; i < nWorkers; i++ )
    {
        if ( WorkerThread )
        {
            ThData[i].p = Gia_ManDup( p );
            Cec_CopyGiaName( p, ThData[i].p );
            ThData[i].iEngine = pEngines[i];
            ThData[i].fWorking = 0;
            ThData[i].fStop    = 0;
            ThData[i].nTimeOut = nTimeOut;
            ThData[i].Result   = -1;
            ThData[i].fVerbose = fVerbose;
            ThData[i].nTimeOutU= nTimeOutU;
            ThData[i].pWlc     = pWlc;
            ThData[i].pUfarArgs= pUfarArgs;
            ThData[i].WorkerId = i;
            ThData[i].StageId  = StageId;
            ThData[i].NetId    = NetId;
            ThData[i].StopReason = 0;
            ThData[i].pShare   = pShare;
            ThData[i].pTrace   = pTrace;
            status = pthread_mutex_init( &ThData[i].Mutex, NULL );
            assert( status == 0 );
            status = pthread_cond_init( &ThData[i].Cond, NULL );
            assert( status == 0 );
            status = pthread_create( WorkerThread + i, NULL, Cec_GiaProveWorkerThread, (void *)(ThData + i) );
            assert( status == 0 );
            continue;
        }
        status = pthread_mutex_lock( &ThData[i].Mutex );
        assert( status == 0 );
        assert( !ThData[i].fStop );
        assert( !ThData[i].fWorking );
        Gia_ManStopP( &ThData[i].p );
        ThData[i].p = Gia_ManDup( p );
        Cec_CopyGiaName( p, ThData[i].p );
        ThData[i].iEngine = pEngines[i];
        ThData[i].nTimeOut = nTimeOut;
        ThData[i].Result   = -1;
        ThData[i].fVerbose = fVerbose;
        ThData[i].nTimeOutU= nTimeOutU;
        ThData[i].pWlc     = pWlc;
        ThData[i].pUfarArgs= pUfarArgs;
        ThData[i].WorkerId = i;
        ThData[i].StageId  = StageId;
        ThData[i].NetId    = NetId;
        ThData[i].StopReason = 0;
        ThData[i].pShare   = pShare;
        ThData[i].pTrace   = pTrace;
        status = pthread_mutex_unlock( &ThData[i].Mutex );
        assert( status == 0 );
    }
    Cec_GiaStartThreads( ThData, nWorkers );
}
static void Cec_GiaStopThreads( Par_ThData_t * ThData, pthread_t * WorkerThread, int nWorkers )
{
    int i, status;
    for ( i = 0; i < nWorkers; i++ )
    {
        status = pthread_mutex_lock( &ThData[i].Mutex );
        assert( status == 0 );
        ThData[i].fStop = 1;
        status = pthread_cond_signal( &ThData[i].Cond );
        assert( status == 0 );
        status = pthread_mutex_unlock( &ThData[i].Mutex );
        assert( status == 0 );
    }
    for ( i = 0; i < nWorkers; i++ )
    {
        status = pthread_join( WorkerThread[i], NULL );
        assert( status == 0 );
        Gia_ManStopP( &ThData[i].p );
        status = pthread_cond_destroy( &ThData[i].Cond );
        assert( status == 0 );
        status = pthread_mutex_destroy( &ThData[i].Mutex );
        assert( status == 0 );
    }
}
static int Cec_GiaWaitThreads( Par_ThData_t * ThData, int nWorkers, Gia_Man_t * p, int RetValue, int * pRetEngine )
{
    int i, status, fWorking;
    for ( i = 0; i < nWorkers; i++ )
    {
        status = pthread_mutex_lock( &ThData[i].Mutex );
        assert( status == 0 );
        fWorking = ThData[i].fWorking;
        if ( RetValue == -1 && !fWorking && ThData[i].Result != -1 )
        {
            RetValue = ThData[i].Result;
            *pRetEngine = ThData[i].iEngine;
            if ( !p->pCexSeq && ThData[i].p->pCexSeq )
                p->pCexSeq = Abc_CexDup( ThData[i].p->pCexSeq, -1 );
        }
        status = pthread_mutex_unlock( &ThData[i].Mutex );
        assert( status == 0 );
        if ( fWorking )
            i = -1;
    }
    return RetValue;
}
    
int Cec_GiaReplayReadParams( char * pFileName, int * pnProcs, int * pnTimeOut, int * pnTimeOut2, int * pnTimeOut3, int * pfUseUif )
{
    Cec_SprovePlan_t Plan;
    if ( !Cec_SproveReplayReadParamsInt( pFileName, &Plan ) )
        return 0;
    if ( pnProcs )
        *pnProcs = Plan.nProcs;
    if ( pnTimeOut )
        *pnTimeOut = Plan.nTimeOut;
    if ( pnTimeOut2 )
        *pnTimeOut2 = Plan.nTimeOut2;
    if ( pnTimeOut3 )
        *pnTimeOut3 = Plan.nTimeOut3;
    if ( pfUseUif )
        *pfUseUif = Plan.fUseUif;
    Cec_SprovePlanFree( &Plan );
    return 1;
}
int Cec_GiaProveTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent, char * pReplayFile, char * pUfarArgs )
{
    Cec_SprovePlan_t Plan;
    int RetValue;
    Cec_SprovePlanDefault( &Plan, nProcs, nTimeOut, nTimeOut2, nTimeOut3, fUseUif, pUfarArgs );
    assert( nProcs >= 1 && nProcs <= 6 );
    assert( nProcs + (fUseUif ? 1 : 0) <= PAR_THR_MAX );
    RetValue = Cec_SproveExecutePlan( p, &Plan, pWlc, fVerbose, fVeryVerbose, fSilent, pReplayFile );
    Cec_SprovePlanFree( &Plan );
    return RetValue;
}
int Cec_GiaReplayTest( Gia_Man_t * p, Wlc_Ntk_t * pWlc, char * pFileName, int fVerbose, int fVeryVerbose, int fSilent )
{
    Cec_SprovePlan_t Plan;
    int RetValue;
    if ( !Cec_SproveReplayReadPlan( pFileName, &Plan ) )
        return -1;
    RetValue = Cec_SproveExecutePlan( p, &Plan, pWlc, fVerbose, fVeryVerbose, fSilent, NULL );
    Cec_SprovePlanFree( &Plan );
    return RetValue;
}

#endif // pthreads are used

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
