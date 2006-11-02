/**CFile****************************************************************

  FileName    [ret_.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: ret_.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes initial values of the new latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeInitialValues( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter, int fVerbose )
{
    Abc_Obj_t * pLatch;
    int * pModel, RetValue, clk, i;
    if ( fVerbose )
        printf( "The number of ANDs in the AIG = %5d.\n", Abc_NtkNodeNum(pNtkMiter) );
    // solve the miter
clk = clock();
    RetValue = Abc_NtkMiterSat( pNtkMiter, (sint64)500000, (sint64)50000000, 0, 0, NULL, NULL );
if ( fVerbose && clock() - clk > 100 )
{
PRT( "SAT solving time", clock() - clk );
}
    // analyze the result
    if ( RetValue == 1 )
        printf( "Abc_NtkRetimeInitialValues(): The problem is unsatisfiable. DC latch values are used.\n" );
    else if ( RetValue == -1 )
        printf( "Abc_NtkRetimeInitialValues(): The SAT problem timed out. DC latch values are used.\n" );
    // set the values of the latches
    pModel = pNtkMiter->pModel;  pNtkMiter->pModel = NULL;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pLatch->pData = (void *)(pModel? (pModel[i]? ABC_INIT_ONE : ABC_INIT_ZERO) : ABC_INIT_DC);
    FREE( pModel );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


