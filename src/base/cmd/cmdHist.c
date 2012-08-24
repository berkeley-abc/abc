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
    static char Buffer[MAX_STR];
    strcpy( Buffer, command );
    if ( command[strlen(command)-1] != '\n' )
        strcat( Buffer, "\n" );
    Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryRead( Abc_Frame_t * p )
{
    char Buffer[1000];
    FILE * pFile;
    assert( Vec_PtrSize(p->aHistory) == 0 );
    pFile = fopen( "abc.history", "rb" );
    if ( pFile == NULL )
    {
//        Abc_Print( 0, "Cannot open file \"abc.history\" for reading.\n" );
        return;
    }
    while ( fgets( Buffer, 1000, pFile ) != NULL )
        Vec_PtrPush( p->aHistory, Extra_UtilStrsav(Buffer) );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cmd_HistoryWrite( Abc_Frame_t * p )
{
    FILE * pFile;
    char * pName; 
    int i;
    pFile = fopen( "abc.history", "wb" );
    if ( pFile == NULL )
    {
        Abc_Print( 0, "Cannot open file \"abc.history\" for writing.\n" );
        return;
    }
    Vec_PtrForEachEntry( char *, p->aHistory, pName, i )
        fputs( pName, pFile );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
ABC_NAMESPACE_IMPL_END

