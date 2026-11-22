/**CFile****************************************************************

  FileName    [absPth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Abstraction package.]

  Synopsis    [Interface to pthreads.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: absPth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "abs.h"
#include "proof/pdr2/pdr2.h"
#include "base/main/main.h"
#include "proof/ssw/ssw.h"


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

#ifdef ABC_USE_PTHREADS
pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

#if defined(ABC_USE_PTHREADS) && ABC_HAS_THREAD_LOCAL

struct Abs_Prover_t_
{
    Aig_Man_t * pAig;
    pthread_t Thread;
    pthread_mutex_t Mutex;
    abctime Deadline;
    int fStop, fProved;
};

static ABC_THREAD_LOCAL Abs_Prover_t * s_pAbsWorker;
static ABC_THREAD_LOCAL Abs_Prover_t * s_pAbsLegacy;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Abs_ProverStop( int RunId )
{
    Abs_Prover_t * p = s_pAbsWorker;
    int Stop;
    (void)RunId;
    pthread_mutex_lock( &p->Mutex );
    Stop = p->fStop;
    pthread_mutex_unlock( &p->Mutex );
    return Stop;
}

static void * Abs_ProverThread( void * pArg )
{
    Abs_Prover_t * p = (Abs_Prover_t *)pArg;
    Abc_Frame_t * pFrame = Abc_FrameCreateChild(), * pPrevious = Abc_FrameEnter(pFrame);
    Pdr2_Par_t Pars;
    int Result;
    s_pAbsWorker = p;
    Pdr2_ManSetDefaultParams( &Pars );
    Pars.iSchedule = PDR2_SCHED_CHECKED;
    Pars.timePolicyStop = p->Deadline;
    Pars.fSilent = Pars.fVerify = Pars.fVerifyComplete = 1;
    Pars.pFuncStop = Abs_ProverStop;
    Result = Pdr2_ManSolveAbstraction( p->pAig, &Pars );
    pthread_mutex_lock( &p->Mutex );
    p->fProved = Result == 1;
    pthread_mutex_unlock( &p->Mutex );
    s_pAbsWorker = NULL;
    Abc_FrameLeave( pPrevious );
    Abc_FrameDestroy( pFrame );
    return NULL;
}

Abs_Prover_t * Gia_GlaProverStart( Gia_Man_t * pGia, int fSimpProver, int fVerbose, abctime Deadline )
{
    Abs_Prover_t * p;
    Aig_Man_t * pReduced;
    Gia_Man_t * pAbs;
    Ssw_Pars_t Pars;
    if ( Deadline && Abc_Clock() >= Deadline ) return NULL;
    p = ABC_CALLOC( Abs_Prover_t, 1 );
    if ( pthread_mutex_init(&p->Mutex, NULL) )
    {
        ABC_FREE( p );
        return NULL;
    }
    pAbs = Gia_ManDupAbsGates( pGia, pGia->vGateClasses );
    Gia_ManCleanValue( pGia );
    p->pAig = Gia_ManToAig( pAbs, 0 );
    Gia_ManStop( pAbs );
    if ( fSimpProver )
    {
        Ssw_ManSetDefaultParams( &Pars );
        Pars.nFramesK = 4;
        if ( Deadline ) Pars.TimeLimit = Abc_MaxInt(1, (int)((Deadline - Abc_Clock()) / CLOCKS_PER_SEC));
        pReduced = Ssw_SignalCorrespondence( p->pAig, &Pars );
        if ( pReduced )
        {
            Aig_ManStop( p->pAig );
            p->pAig = pReduced;
        }
    }
    p->Deadline = Deadline;
    if ( (!Deadline || Abc_Clock() < Deadline) && !pthread_create(&p->Thread, NULL, Abs_ProverThread, p) )
    {
        if ( fVerbose ) Abc_Print( 1, "Trying to prove the abstraction with PDR2.\n" );
        return p;
    }
    Aig_ManStop( p->pAig );
    pthread_mutex_destroy( &p->Mutex );
    ABC_FREE( p );
    return NULL;
}
int Gia_GlaProverCheck( Abs_Prover_t * p )
{
    int Result;
    if ( !p ) return 0;
    pthread_mutex_lock( &p->Mutex );
    Result = p->fProved;
    p->fProved = 0;
    pthread_mutex_unlock( &p->Mutex );
    return Result;
}
void Gia_GlaProverStop( Abs_Prover_t ** pp )
{
    Abs_Prover_t * p = *pp;
    if ( !p ) return;
    pthread_mutex_lock( &p->Mutex );
    p->fStop = 1;
    pthread_mutex_unlock( &p->Mutex );
    pthread_join( p->Thread, NULL );
    pthread_mutex_destroy( &p->Mutex );
    Aig_ManStop( p->pAig );
    ABC_FREE( *pp );
}

void Gia_GlaProveAbsracted( Gia_Man_t * p, int fSimpProver, int fVerbose )
{
    Gia_GlaProverStop( &s_pAbsLegacy );
    s_pAbsLegacy = Gia_GlaProverStart( p, fSimpProver, fVerbose, 0 );
}
void Gia_GlaProveCancel( int fVerbose ) { (void)fVerbose; Gia_GlaProverStop( &s_pAbsLegacy ); }
int Gia_GlaProveCheck( int fVerbose ) { (void)fVerbose; return Gia_GlaProverCheck(s_pAbsLegacy); }

#else

Abs_Prover_t * Gia_GlaProverStart( Gia_Man_t * p, int fSimpProver, int fVerbose, abctime Deadline ) { return NULL; }
int Gia_GlaProverCheck( Abs_Prover_t * p ) { return 0; }
void Gia_GlaProverStop( Abs_Prover_t ** pp ) {}
void Gia_GlaProveAbsracted( Gia_Man_t * p, int fSimpProver, int fVerbose ) {}
void Gia_GlaProveCancel( int fVerbose ) {}
int Gia_GlaProveCheck( int fVerbose ) { return 0; }

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

