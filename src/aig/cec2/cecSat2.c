/**CFile****************************************************************

  FileName    [cecSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Backend calling the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: cecSat.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"
#include "cnf.h"
#include "../../sat/lsat/solver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes CNF into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
solver * Cnf_WriteIntoSolverNew( Cnf_Dat_t * p )
{
    solver * pSat;
    int i, status;
    pSat = solver_new();
    for ( i = 0; i < p->nVars; i++ )
        solver_newVar( pSat );
    for ( i = 0; i < p->nClauses; i++ )
    {
        if ( !solver_addClause( pSat, p->pClauses[i+1]-p->pClauses[i], p->pClauses[i] ) )
        {
            solver_delete( pSat );
            return NULL;
        }
    }
    status = solver_simplify(pSat);
    if ( status == 0 )
    {
        solver_delete( pSat );
        return NULL;
    }
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Adds the OR-clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_DataWriteAndClausesNew( void * p, Cnf_Dat_t * pCnf )
{
/*
    sat_solver * pSat = p;
    Aig_Obj_t * pObj;
    int i, Lit;
    Aig_ManForEachPo( pCnf->pMan, pObj, i )
    {
        Lit = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
        if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
            return 0;
    }
*/
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds the OR-clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_DataWriteOrClauseNew( solver * pSat, Cnf_Dat_t * pCnf )
{
    Aig_Obj_t * pObj;
    int i, * pLits;
    pLits = ALLOC( int, Aig_ManPoNum(pCnf->pMan) );
    Aig_ManForEachPo( pCnf->pMan, pObj, i )
        pLits[i] = solver_mkLit_args( pCnf->pVarNums[pObj->Id], 0 );
    if ( !solver_addClause( pSat, Aig_ManPoNum(pCnf->pMan), pLits ) )
    {
        free( pLits );
        return 0;
    }
    free( pLits );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the given clause in a file in DIMACS format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_SolverPrintStatsNew( FILE * pFile, solver * pSat )
{
//    printf( "starts        : %8d\n", solver_num_assigns(pSat) );
    printf( "vars          : %8d\n", solver_num_vars(pSat) );
    printf( "clauses       : %8d\n", solver_num_clauses(pSat) );
    printf( "conflicts     : %8d\n", solver_num_learnts(pSat) );
}

/**Function*************************************************************

  Synopsis    [Returns a counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Sat_SolverGetModelNew( solver * pSat, int * pVars, int nVars )
{
    int * pModel;
    int i;
    pModel = ALLOC( int, nVars+1 );
    for ( i = 0; i < nVars; i++ )
    {
        assert( pVars[i] >= 0 && pVars[i] < solver_num_vars(pSat) );
        pModel[i] = (int)(solver_modelValue_Var( pSat, pVars[i] ) == solver_l_True);
    }
    return pModel;    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_RunSat( Aig_Man_t * pMan, sint64 nConfLimit, sint64 nInsLimit, int fFlipBits, int fAndOuts, int fVerbose )
{
    solver * pSat;
    Cnf_Dat_t * pCnf;
    int status, RetValue, clk = clock();
    Vec_Int_t * vCiIds;

    assert( Aig_ManRegNum(pMan) == 0 );
    pMan->pData = NULL;

    // derive CNF
    pCnf = Cnf_Derive( pMan, Aig_ManPoNum(pMan) );
//    pCnf = Cnf_DeriveSimple( pMan, Aig_ManPoNum(pMan) );

    // convert into SAT solver
    pSat = Cnf_WriteIntoSolverNew( pCnf );
    if ( pSat == NULL )
    {
        Cnf_DataFree( pCnf );
        return 1;
    }


    if ( fAndOuts )
    {
        assert( 0 );
        // assert each output independently
        if ( !Cnf_DataWriteAndClausesNew( pSat, pCnf ) )
        {
            solver_delete( pSat );
            Cnf_DataFree( pCnf );
            return 1;
        }
    }
    else
    {
        // add the OR clause for the outputs
        if ( !Cnf_DataWriteOrClauseNew( pSat, pCnf ) )
        {
            solver_delete( pSat );
            Cnf_DataFree( pCnf );
            return 1;
        }
    }
    vCiIds = Cnf_DataCollectPiSatNums( pCnf, pMan );
    Cnf_DataFree( pCnf );


//    printf( "Created SAT problem with %d variable and %d clauses. ", sat_solver_nvars(pSat), sat_solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );

    // simplify the problem
    clk = clock();
    status = solver_simplify(pSat);
//    printf( "Simplified the problem to %d variables and %d clauses. ", sat_solver_nvars(pSat), sat_solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );
    if ( status == 0 )
    {
        Vec_IntFree( vCiIds );
        solver_delete( pSat );
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return 1;
    }

    // solve the miter
    clk = clock();
    if ( fVerbose )
        solver_set_verbosity( pSat, 1 );
    status = solver_solve( pSat, 0, NULL );
    if ( status == solver_l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if ( status == solver_l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if ( status == solver_l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }
    else
        assert( 0 );
//    PRT( "SAT sat_solver time", clock() - clk );
//    printf( "The number of conflicts = %d.\n", (int)pSat->sat_solver_stats.conflicts );
 
    // if the problem is SAT, get the counterexample
    if ( status == solver_l_True )
    {
        pMan->pData = Sat_SolverGetModelNew( pSat, vCiIds->pArray, vCiIds->nSize );
    }
    // free the sat_solver
    if ( fVerbose )
        Sat_SolverPrintStatsNew( stdout, pSat );
//sat_solver_store_write( pSat, "trace.cnf" );
//sat_solver_store_free( pSat );
    solver_delete( pSat );
    Vec_IntFree( vCiIds );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

