/**CFile****************************************************************

  FileName    [fraigCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fraigCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Aig_ProofType_t Aig_FraigProveOutput( Aig_Man_t * pMan );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Top-level equivalence checking procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_ProofType_t Aig_FraigProve( Aig_Man_t * pMan )
{
    Aig_ProofType_t RetValue;
    int clk, status;
    
    // create the solver
    RetValue = Aig_ClauseSolverStart( pMan );
    if ( RetValue != AIG_PROOF_NONE )
        return RetValue;
    // perform solving

    // simplify the problem
    clk = clock();
    status = solver_simplify(pMan->pSat);
    if ( status == 0 )
    {
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return AIG_PROOF_UNSAT;
    }

    // try to prove the output
    RetValue = Aig_FraigProveOutput( pMan );
    if ( RetValue != AIG_PROOF_TIMEOUT )
        return RetValue;

    // create equivalence classes
    Aig_EngineSimulateRandomFirst( pMan );
    // reduce equivalence classes using simulation
    Aig_EngineSimulateFirst( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Top-level equivalence checking procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_ProofType_t Aig_FraigProveOutput( Aig_Man_t * pMan )
{
    Aig_ProofType_t RetValue;
    int clk, status;

    // solve the miter
    clk = clock();
    pMan->pSat->verbosity = pMan->pParam->fSatVerbose;
    status = solver_solve( pMan->pSat, NULL, NULL, 0, 0 );//pMan->pParam->nConfLimit, pMan->pParam->nInsLimit );
    if ( status == l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = AIG_PROOF_TIMEOUT;
    }
    else if ( status == l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = AIG_PROOF_SAT;
    }
    else if ( status == l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = AIG_PROOF_UNSAT;
    }
    else
        assert( 0 );
//    PRT( "SAT solver time", clock() - clk );

    // if the problem is SAT, get the counterexample
    if ( status == l_True )
    {
        if ( pMan->pModel ) free( pMan->pModel );
        pMan->pModel = solver_get_model( pMan->pSat, pMan->vPiSatNums->pArray, pMan->vPiSatNums->nSize );
        printf( "%d %d %d %d\n", pMan->pModel[0], pMan->pModel[1], pMan->pModel[2], pMan->pModel[3] );
    }
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


