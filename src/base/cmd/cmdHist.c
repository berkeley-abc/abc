/**CFile****************************************************************

  FileName    [cmdHist.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures working with history.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cmdHist.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "cmd.h"
#include "cmdInt.h"

#ifdef ABC_USE_PTHREADS
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

#ifdef ABC_USE_PTHREADS
static pthread_mutex_t s_HistoryMutex = PTHREAD_MUTEX_INITIALIZER;
static void Cmd_HistoryLock()   { int Status = pthread_mutex_lock( &s_HistoryMutex );   assert( Status == 0 ); (void)Status; }
static void Cmd_HistoryUnlock() { int Status = pthread_mutex_unlock( &s_HistoryMutex ); assert( Status == 0 ); (void)Status; }
#else
static void Cmd_HistoryLock()   {}
static void Cmd_HistoryUnlock() {}
#endif


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryAddCommand(    Abc_Frame_t * p, const char * command )
{
    int nLastLooked =    10;  // do not add history if the same entry appears among the last entries
    int nLastSaved  = 20000;  // when saving a file, save no more than this number of last entries
    char Buffer[ABC_MAX_STR];
    int Len;
    if ( p->fBatchMode )
        return;
    Len = strlen(command);
    strcpy( Buffer, command );
    if ( Len > 0 && Buffer[Len-1] == '\n' )
        Buffer[Len-1] = 0;
    if ( strlen(Buffer) > 3 &&
         strncmp(Buffer,"set",3) && 
         strncmp(Buffer,"unset",5) && 
         strncmp(Buffer,"time",4) && 
         strncmp(Buffer,"quit",4) && 
         strncmp(Buffer,"alias",5) && 
         strncmp(Buffer,"source abc.rc",13) && 
         strncmp(Buffer,"source ..\\abc.rc",16) && 
         strncmp(Buffer,"history",7) && strncmp(Buffer,"hi ", 3) && strcmp(Buffer,"hi") &&
         Buffer[strlen(Buffer)-1] != '?' )
    {
        char * pStr = NULL;
        int i, Start = Abc_MaxInt( 0, Vec_PtrSize(p->aHistory) - nLastLooked );
        // do not enter if the same command appears among nLastLooked commands
        Vec_PtrForEachEntryStart( char *, p->aHistory, pStr, i, Start )
            if ( !strcmp(pStr, Buffer) )
                break;
        if ( i == Vec_PtrSize(p->aHistory) )
        { // add new entry
            Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
            Cmd_HistoryWrite( p, nLastSaved );
        }
        else
        { // put at the end
            Vec_PtrRemove( p->aHistory, pStr );
            Vec_PtrPush( p->aHistory, pStr );
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryRead( Abc_Frame_t * p )
{
#if !defined(ABC_NO_HISTORY)
    char Buffer[ABC_MAX_STR];
    FILE * pFile;
    assert( Vec_PtrSize(p->aHistory) == 0 );
    Cmd_HistoryLock();
    pFile = fopen( "abc.history", "rb" );
    if ( pFile == NULL )
    {
        Cmd_HistoryUnlock();
        return;
    }
    while ( fgets( Buffer, ABC_MAX_STR, pFile ) != NULL )
    {
        int Len = strlen(Buffer);
        if ( Len > 0 && Buffer[Len-1] == '\n' )
            Buffer[Len-1] = 0;
        Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
    }
    fclose( pFile );
    p->iStartHistory = Vec_PtrSize(p->aHistory);
    Cmd_HistoryUnlock();
#endif
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryWrite( Abc_Frame_t * p, int Limit )
{
#if !defined(ABC_NO_HISTORY)
    FILE * pFile;
    char * pStr; 
    int i;
    Cmd_HistoryLock();
    if ( 1 )
    {
        pFile = fopen( "abc.history", "ab" );
        if ( pFile == NULL )
        {
            Abc_Print( 0, "Cannot open file \"abc.history\" for writing.\n" );
            Cmd_HistoryUnlock();
            return;
        }
        Vec_PtrForEachEntryStart( char *, p->aHistory, pStr, i, p->iStartHistory )
            fprintf( pFile, "%s\n", pStr );
        fclose( pFile );
        p->iStartHistory = Vec_PtrSize(p->aHistory);
    }
    if ( Vec_PtrSize(p->aHistory) > Limit + 1000 )
    {
        char Buffer[ABC_MAX_STR];
        Vec_Ptr_t * aHistoryAll = Vec_PtrAlloc( Vec_PtrSize(p->aHistory) );
        Vec_Ptr_t * aHistory;
        pFile = fopen( "abc.history", "rb" );
        if ( pFile == NULL )
        {
            Abc_Print( 0, "Cannot open file \"abc.history\" for reading.\n" );
            Vec_PtrFree( aHistoryAll );
            Cmd_HistoryUnlock();
            return;
        }
        while ( fgets(Buffer, ABC_MAX_STR, pFile) != NULL )
        {
            int Len = strlen(Buffer);
            if ( Len > 0 && Buffer[Len-1] == '\n' )
                Buffer[Len-1] = 0;
            Vec_PtrPush( aHistoryAll, Abc_UtilStrsav(Buffer) );
        }
        fclose( pFile );
        pFile = fopen( "abc.history", "wb" );
        if ( pFile == NULL )
        {
            Abc_Print( 0, "Cannot open file \"abc.history\" for writing.\n" );
            Vec_PtrFreeFree( aHistoryAll );
            Cmd_HistoryUnlock();
            return;
        }
        Limit = Abc_MaxInt( 0, Vec_PtrSize(aHistoryAll)-Limit );
        aHistory = Vec_PtrAlloc( Vec_PtrSize(aHistoryAll)-Limit );
        Vec_PtrForEachEntryStart( char *, aHistoryAll, pStr, i, Limit ) {
            fprintf( pFile, "%s\n", pStr );
            Vec_PtrPush( aHistory, pStr );
        }
        fclose( pFile );
        Vec_PtrForEachEntryStop( char *, aHistoryAll, pStr, i, Limit )
            ABC_FREE( pStr );
        Vec_PtrFree( aHistoryAll );
        Vec_PtrFreeFree( p->aHistory );
        p->aHistory = aHistory;
        p->iStartHistory = Vec_PtrSize(p->aHistory);
    }
    Cmd_HistoryUnlock();
#endif
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryPrint( Abc_Frame_t * p, int Limit )
{
#if !defined(ABC_NO_HISTORY) 
    char * pStr; 
    int i;
    Limit = Abc_MaxInt( 0, Vec_PtrSize(p->aHistory)-Limit );
    printf( "================== Command history ==================\n" );
    Vec_PtrForEachEntryStart( char *, p->aHistory, pStr, i, Limit )
        printf( "%s\n", pStr );
    printf( "=====================================================\n" );
#endif
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
ABC_NAMESPACE_IMPL_END
