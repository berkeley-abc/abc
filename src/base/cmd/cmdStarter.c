/**CFile****************************************************************

  FileName    [cmdStarter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Command to start many instances of ABC in parallel.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cmdStarter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "misc/util/abc_global.h"

// comment out this line to disable pthreads
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

#ifndef ABC_USE_PTHREADS

void Cmd_RunStarter( char * pFileName, int nCores ) {}

#else // pthreads are used

// the number of concurrently running threads
static volatile int nThreadsRunning = 0;

// mutex to control access to the number of threads
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedures executes one call to system().]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_RunThread( void * pCommand )
{
    int status;
    // perform the call
    if ( system( (char *)pCommand ) )
    {
        fprintf( stderr, "The following command has returned non-zero exit status:\n" );
        fprintf( stderr, "\"%s\"\n\n", (char *)pCommand );
        fflush( stdout );
    }
    free( pCommand );

    // decrement the number of threads runining 
    status = pthread_mutex_lock(&mutex);   assert(status == 0);
    nThreadsRunning--;
    status = pthread_mutex_unlock(&mutex); assert(status == 0);

    // quit this thread
    //printf("...Finishing %s\n", (char *)Command);
    pthread_exit( NULL );
    assert(0);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Takes file with commands to be executed and the number of CPUs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_RunStarter( char * pFileName, int nCores )
{
    FILE * pFile, * pOutput = stdout;
    pthread_t * pThreadIds;
    char * BufferCopy, * Buffer;
    int nLines, LineMax, Line;
    int i, c, status, Counter;
    clock_t clk = clock();

    // check the number of cores
    if ( nCores < 2 )
    {
        fprintf( pOutput, "The number of cores (%d) should be more than 1.\n", nCores ); 
        return; 
    }

    // open the file and make sure it is available
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    { 
        fprintf( pOutput, "Input file \"%s\" cannot be opened.\n", pFileName ); 
        return; 
    }

    // count the number of lines and the longest line
    nLines = LineMax = Line = 0;
    while ( (c = fgetc(pFile)) != EOF )
    {
        Line++;
        if ( c != '\n' )
            continue;
        nLines++;
        LineMax = Abc_MaxInt( LineMax, Line );
        Line = 0;       
    }
    LineMax += 10;
    nLines += 10;

    // allocate storage
    Buffer = ABC_ALLOC( char, LineMax );
    pThreadIds = ABC_ALLOC( pthread_t, nLines );

    // read commands and execute at most <num> of them at a time
    rewind( pFile );
    for ( i = 0; fgets( Buffer, LineMax, pFile ) != NULL; i++ )
    {
        // get the command from the file
        if ( Buffer[0] == '\n' || Buffer[0] == '\r' || Buffer[0] == '\t' || 
             Buffer[0] == ' ' || Buffer[0] == '#')
        {
            continue;
        }

        if ( Buffer[strlen(Buffer)-1] == '\n' )
            Buffer[strlen(Buffer)-1] = 0;
        if ( Buffer[strlen(Buffer)-1] == '\r' )
            Buffer[strlen(Buffer)-1] = 0;

        // wait till there is an empty thread
        while ( 1 )
        {
            status = pthread_mutex_lock(&mutex);   assert(status == 0);
            Counter = nThreadsRunning;
            status = pthread_mutex_unlock(&mutex); assert(status == 0);
            if ( Counter < nCores - 1 )
                break;
//            Sleep( 100 );
        }

        // increament the number of threads running
        status = pthread_mutex_lock(&mutex);   assert(status == 0);
        nThreadsRunning++;
        status = pthread_mutex_unlock(&mutex); assert(status == 0);

        printf( "Calling:  %s\n", (char *)Buffer );  
        fflush( stdout );

        // create thread to execute this command
        BufferCopy = Abc_UtilStrsav( Buffer );
        status = pthread_create( &pThreadIds[i], NULL, Abc_RunThread, (void *)BufferCopy );  assert(status == 0);
        assert( i < nLines );
    }
    ABC_FREE( pThreadIds );
    ABC_FREE( Buffer );
    fclose( pFile );

    // wait for all the threads to finish
    while ( 1 )
    {
        status = pthread_mutex_lock(&mutex);   assert(status == 0);
        Counter = nThreadsRunning;
        status = pthread_mutex_unlock(&mutex); assert(status == 0);
        if ( Counter == 0 )
            break;
    }

    // cleanup
    status = pthread_mutex_destroy(&mutex);   assert(status == 0);
//    assert(mutex == NULL);
    printf( "Finished processing commands in file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Total wall time", clock() - clk );
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

