/**CFile****************************************************************

  FileName    [abcFpgaFast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Fast FPGA mapper.]

  Author      [Sungmin Cho]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFpgaFast.c,v 1.00 2006/09/02 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fast FPGA mapping of the network.]

  Description [Takes the AIG to be mapped, the LUT size, and verbosity
  flag. Produces the new network by fast FPGA mapping of the current 
  network. If the current network in ABC in not an AIG, the user should 
  run command "strash" to make sure that the current network into an AIG 
  before calling this procedure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFpgaFast( Abc_Ntk_t * pNtk, int nLutSize, int fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;
    int i;

    // make sure the network is an AIG
    assert( Abc_NtkIsStrash(pNtk) );

    // iterate over the nodes in the network
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
    }

    // create the new network after mapping
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );

    // here we need to create nodes of the new network
    
    // make sure that the final network passes the test
    if ( pNtkNew != NULL && !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkFastMap: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


