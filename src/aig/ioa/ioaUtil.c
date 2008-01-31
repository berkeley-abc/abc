/**CFile****************************************************************

  FileName    [ioaUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read binary AIGER format developed by
  Armin Biere, Johannes Kepler University (http://fmv.jku.at/)]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - December 16, 2006.]

  Revision    [$Id: ioaUtil.c,v 1.00 2006/12/16 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the file size.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ioa_FileSize( char * pFileName )
{
    FILE * pFile;
    int nFileSize;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Ioa_FileSize(): The file is unavailable (absent or open).\n" );
        return 0;
    }
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile ); 
    fclose( pFile );
    return nFileSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ioa_FileNameGeneric( char * FileName )
{
    char * pDot;
    char * pUnd;
    char * pRes;
    
    // find the generic name of the file
    pRes = Aig_UtilStrsav( FileName );
    // find the pointer to the "." symbol in the file name
//  pUnd = strstr( FileName, "_" );
    pUnd = NULL;
    pDot = strstr( FileName, "." );
    if ( pUnd )
        pRes[pUnd - FileName] = 0;
    else if ( pDot )
        pRes[pDot - FileName] = 0;
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Returns the time stamp.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ioa_TimeStamp()
{
    static char Buffer[100];
    char * TimeStamp;
    time_t ltime;
    // get the current time
    time( &ltime );
    TimeStamp = asctime( localtime( &ltime ) );
    TimeStamp[ strlen(TimeStamp) - 1 ] = 0;
    strcpy( Buffer, TimeStamp );
    return Buffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


