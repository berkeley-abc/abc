/**CFile****************************************************************

  FileName    [giaAbsPth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Interface to pthreads.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsPth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "aig/ioa/ioa.h"
#include "proof/pdr/pdr.h"

// comment this out to disable pthreads
#define ABC_USE_PTHREADS

#ifdef ABC_USE_PTHREADS

#ifdef WIN32
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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start and stop proving abstracted model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#ifndef ABC_USE_PTHREADS

void Gia_Ga2ProveAbsracted( char * pFileName, int fVerbose ) {}
void Gia_Ga2ProveCancel( int fVerbose )                      {}
void Gia_Ga2ProveFinish( int fVerbose )                      {}
int  Gia_Ga2ProveCheck( int fVerbose )                       { return 0; }

#else // pthreads are used

// information given to the thread
typedef struct Abs_Pair_t_
{
    char * pFileName;
    int    fVerbose;
    int    RunId;
} Abs_Pair_t;

// the last valid thread
static int g_nRunIds = 0;
int Abs_CallBackToStop( int RunId ) { assert( RunId <= g_nRunIds ); return RunId < g_nRunIds; }


int Pdr_ManSolve_test( Aig_Man_t * pAig, Pdr_Par_t * pPars, Abc_Cex_t ** ppCex )
{
    char * p = ABC_ALLOC( char, 111 );
    while ( 1 )
    {
        if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) )
            break;
    }
    ABC_FREE( p );
    return -1;
}

static int g_fAbstractionProved = 0;
void * Abs_ProverThread( void * pArg )
{
    Abs_Pair_t * pPair = (Abs_Pair_t *)pArg;
    Pdr_Par_t Pars, * pPars = &Pars;
    Aig_Man_t * pAig, * pTemp;
    int RetValue;
    pAig = Ioa_ReadAiger( pPair->pFileName, 0 );
    if ( pAig == NULL )
        Abc_Print( 1, "\nCannot open file \"%s\".\n", pPair->pFileName );
    else
    {
        // synthesize abstraction
        pAig = Aig_ManScl( pTemp = pAig, 1, 1, 0, -1, -1, 0, 0 );
        Aig_ManStop( pTemp );
        // call PDR
        Pdr_ManSetDefaultParams( pPars );
        pPars->fSilent = 1;
        pPars->RunId = pPair->RunId;
        pPars->pFuncStop = Abs_CallBackToStop;
        RetValue = Pdr_ManSolve( pAig, pPars, NULL );
//        RetValue = Pdr_ManSolve_test( pAig, pPars, NULL );
        // update the result
        g_fAbstractionProved = (RetValue == 1);
        // free memory
        Aig_ManStop( pAig );
        // quit this thread
        if ( pPair->fVerbose )
        {
            if ( RetValue == 1 )
                Abc_Print( 1, "\nProved abstraction %d.\n", pPair->RunId );
            else if ( RetValue == 0 )
                Abc_Print( 1, "\nDisproved abstraction %d.\n", pPair->RunId );
            else if ( RetValue == -1 )
                Abc_Print( 1, "\nCancelled abstraction %d.\n", pPair->RunId );
            else assert( 0 );
        }
    }
    ABC_FREE( pPair->pFileName );
    ABC_FREE( pPair );
    // quit this thread
    pthread_exit( NULL );
    assert(0);
    return NULL;
}
void Gia_Ga2ProveAbsracted( char * pFileName, int fVerbose )
{
    Abs_Pair_t * pPair;
    pthread_t ProverThread;
    int RetValue;
    assert( pFileName != NULL );
    g_fAbstractionProved = 0;
    // disable verbosity
    fVerbose = 0;
    // create thread
    pPair = ABC_CALLOC( Abs_Pair_t, 1 );
    pPair->pFileName = Abc_UtilStrsav( (void *)pFileName );
    pPair->fVerbose = fVerbose;
    pPair->RunId = ++g_nRunIds;
    if ( fVerbose )  Abc_Print( 1, "\nTrying to prove abstraction %d.\n", pPair->RunId );
    RetValue = pthread_create( &ProverThread, NULL, Abs_ProverThread, pPair );
    assert( RetValue == 0 );
}
void Gia_Ga2ProveCancel( int fVerbose )
{
    g_nRunIds++;
}
void Gia_Ga2ProveFinish( int fVerbose )
{
    g_fAbstractionProved = 0;
}
int Gia_Ga2ProveCheck( int fVerbose )
{
    return g_fAbstractionProved;
}

#endif


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

