/**CFile****************************************************************

  FileName    [ioRead.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedure to read network from file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioRead.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Read the network from a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_Read( char * pFileName, int fCheck )
{
    Abc_Ntk_t * pNtk, * pTemp;
    // set the new network
    if ( Extra_FileNameCheckExtension( pFileName, "blif" ) )
        pNtk = Io_ReadBlif( pFileName, fCheck );
    else if ( Extra_FileNameCheckExtension( pFileName, "v" ) )
        pNtk = Io_ReadVerilog( pFileName, fCheck );
    else if ( Extra_FileNameCheckExtension( pFileName, "bench" ) )
        pNtk = Io_ReadBench( pFileName, fCheck );
    else if ( Extra_FileNameCheckExtension( pFileName, "edf" ) )
        pNtk = Io_ReadEdif( pFileName, fCheck );
    else if ( Extra_FileNameCheckExtension( pFileName, "pla" ) )
        pNtk = Io_ReadPla( pFileName, fCheck );
    else if ( Extra_FileNameCheckExtension( pFileName, "eqn" ) )
        pNtk = Io_ReadEqn( pFileName, fCheck );
    else 
    {
        fprintf( stderr, "Unknown file format\n" );
        return NULL;
    }
    if ( pNtk == NULL )
        return NULL;

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( stdout, "Converting to logic network after reading has failed.\n" );
        return NULL;
    }
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



