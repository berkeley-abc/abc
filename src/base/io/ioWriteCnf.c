/**CFile****************************************************************

  FileName    [ioWriteCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to output CNF of the miter cone.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteCnf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Write the miter cone into a CNF file for the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteCnf( Abc_Ntk_t * pNtk, char * pFileName )
{
    solver * pSat;
    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( stdout, "Io_WriteCnf(): Currently can only process logic networks with BDDs.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        fprintf( stdout, "Io_WriteCnf(): Currently can only solve the miter (the network with one PO).\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) != 0 )
    {
        fprintf( stdout, "Io_WriteCnf(): Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    }
    // create solver with clauses
    pSat = Abc_NtkMiterSatCreate( pNtk );
    // write the clauses
    Asat_SolverWriteDimacs( pSat, pFileName );
    // free the solver
    solver_delete( pSat );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


