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

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

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
    int nLastLooked = 10;   // defines how many entries back are looked
    int nLastSaved  = 100;  // defines how many last entries are saved

    char Buffer[ABC_MAX_STR];
    int Len = strlen(command);
    strcpy( Buffer, command );
    if ( Buffer[Len-1] == '\n' )
        Buffer[Len-1] = 0;
    if ( strncmp(Buffer,"set",3) && 
         strncmp(Buffer,"quit",4) && 
         strncmp(Buffer,"source",6) && 
         strncmp(Buffer,"history",7) && strncmp(Buffer,"hi ", 3) && strcmp(Buffer,"hi") )
    {
        char * pStr;
        int i;
        // do not enter if the same command appears among the last five commands
        Vec_PtrForEachEntryStart( char *, p->aHistory, pStr, i, Abc_MaxInt(0, Vec_PtrSize(p->aHistory)-nLastLooked) )
            if ( !strcmp(pStr, Buffer) )
                break;
        if ( i == Vec_PtrSize(p->aHistory) )
        {
            Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
            Cmd_HistoryWrite( p, nLastSaved );
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
    char Buffer[ABC_MAX_STR];
    FILE * pFile;
    assert( Vec_PtrSize(p->aHistory) == 0 );
    pFile = fopen( "abc.history", "rb" );
    if ( pFile == NULL )
    {
//        Abc_Print( 0, "Cannot open file \"abc.history\" for reading.\n" );
        return;
    }
    while ( fgets( Buffer, ABC_MAX_STR, pFile ) != NULL )
    {
        int Len = strlen(Buffer);
        if ( Buffer[Len-1] == '\n' )
            Buffer[Len-1] = 0;
        Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
    }
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryWrite( Abc_Frame_t * p, int Limit )
{
    FILE * pFile;
    char * pStr; 
    int i;
    pFile = fopen( "abc.history", "wb" );
    if ( pFile == NULL )
    {
        Abc_Print( 0, "Cannot open file \"abc.history\" for writing.\n" );
        return;
    }
    Limit = Abc_MaxInt( 0, Vec_PtrSize(p->aHistory)-Limit );
    Vec_PtrForEachEntryStart( char *, p->aHistory, pStr, i, Limit )
        fprintf( pFile, "%s\n", pStr );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
ABC_NAMESPACE_IMPL_END

