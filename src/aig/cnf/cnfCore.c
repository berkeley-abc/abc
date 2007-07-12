/**CFile****************************************************************

  FileName    [cnfCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG-to-CNF conversion.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: cnfCore.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cnf.h"

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
Cnf_Dat_t * Cnf_Derive( Cnf_Man_t * p, Aig_Man_t * pAig )
{
    Aig_MmFixed_t * pMemCuts;
    Cnf_Dat_t * pCnf = NULL;
    Vec_Ptr_t * vMapped;
    int nIters = 2;
    int clk;

    // connect the managers
    p->pManAig = pAig;

    // generate cuts for all nodes, assign cost, and find best cuts
clk = clock();
    pMemCuts = Dar_ManComputeCuts( pAig );
PRT( "Cuts", clock() - clk );
/*
    // iteratively improve area flow
    for ( i = 0; i < nIters; i++ )
    {
clk = clock();
        Cnf_ManScanMapping( p, 0 );
        Cnf_ManMapForCnf( p );
PRT( "iter ", clock() - clk );
    }
*/
    // write the file
    vMapped = Aig_ManScanMapping( p, 1 );
    Vec_PtrFree( vMapped );

clk = clock();
    Cnf_ManTransferCuts( p );

    Cnf_ManPostprocess( p );
    Cnf_ManScanMapping( p, 0 );
/*
    Cnf_ManPostprocess( p );
    Cnf_ManScanMapping( p, 0 );
    Cnf_ManPostprocess( p );
    Cnf_ManScanMapping( p, 0 );
*/
PRT( "Ext ", clock() - clk );

/*
    vMapped = Cnf_ManScanMapping( p, 1 );
    pCnf = Cnf_ManWriteCnf( p, vMapped );
    Vec_PtrFree( vMapped );

    // clean up
    Cnf_ManFreeCuts( p );
    Dar_ManCutsFree( pAig );
    return pCnf;
*/
    Aig_MmFixedStop( pMemCuts, 0 );
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


