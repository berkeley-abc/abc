/**CFile****************************************************************

  FileName    [abcSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to solve the miter using the internal SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  Abc_NodeAddClauses( solver * pSat, char * pSop0, char * pSop1, Abc_Obj_t * pNode, Vec_Int_t * vVars );
static int  Abc_NodeAddClausesTop( solver * pSat, Abc_Obj_t * pNode, Vec_Int_t * vVars );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using an internal SAT solver.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterSat( Abc_Ntk_t * pNtk, int nSeconds, int fVerbose )
{
    solver * pSat;
    lbool   status;
    int RetValue, clk;

    assert( Abc_NtkIsBddLogic(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    if ( Abc_NtkPoNum(pNtk) > 1 )
        fprintf( stdout, "Warning: The miter has %d outputs. SAT will try to prove all of them.\n", Abc_NtkPoNum(pNtk) );

    // load clauses into the solver
    clk = clock();
    pSat = Abc_NtkMiterSatCreate( pNtk );
    if ( pSat == NULL )
        return 1;
//    printf( "Created SAT problem with %d variable and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );

    // simplify the problem
    clk = clock();
    status = solver_simplify(pSat);
//    printf( "Simplified the problem to %d variables and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );
    if ( status == 0 )
    {
        solver_delete( pSat );
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return 1;
    }

    // solve the miter
    clk = clock();
    if ( fVerbose )
        pSat->verbosity = 1;
    status = solver_solve( pSat, NULL, NULL, nSeconds );
    if ( status == l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if ( status == l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if ( status == l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }
    else
        assert( 0 );
//    PRT( "SAT solver time", clock() - clk );

    // if the problem is SAT, get the counterexample
    if ( status == l_True )
    {
        Vec_Int_t * vCiIds = Abc_NtkGetCiIds( pNtk );
        pNtk->pModel = solver_get_model( pSat, vCiIds->pArray, vCiIds->nSize );
        Vec_IntFree( vCiIds );
    }
    // free the solver
    solver_delete( pSat );
    return RetValue;
}
 
/**Function*************************************************************

  Synopsis    [Sets up the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
solver * Abc_NtkMiterSatCreate( Abc_Ntk_t * pNtk )
{
    solver * pSat;
    Extra_MmFlex_t * pMmFlex;
    Abc_Obj_t * pNode;
    Vec_Str_t * vCube;
    Vec_Int_t * vVars;
    char * pSop0, * pSop1;
    int i;

    assert( Abc_NtkIsBddLogic(pNtk) );

    // start the data structures
    pSat    = solver_new();
    pMmFlex = Extra_MmFlexStart();
    vCube   = Vec_StrAlloc( 100 );
    vVars   = Vec_IntAlloc( 100 );

    // add clauses for each internal nodes
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        // derive SOPs for both phases of the node
        Abc_NodeBddToCnf( pNode, pMmFlex, vCube, &pSop0, &pSop1 );
        // add the clauses to the solver
        if ( !Abc_NodeAddClauses( pSat, pSop0, pSop1, pNode, vVars ) )
        {
            solver_delete( pSat );
            return NULL;
        }
    }
    // add clauses for the POs
    if ( !Abc_NodeAddClausesTop( pSat, Abc_NtkPo(pNtk, Abc_NtkPoNum(pNtk)-1), vVars ) )
    {
        solver_delete( pSat );
        return NULL;
    }
//    Asat_SolverWriteDimacs( pSat, "test.cnf", NULL, NULL, 0 );

    // delete
    Vec_StrFree( vCube );
    Vec_IntFree( vVars );
    Extra_MmFlexStop( pMmFlex, 0 );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Adds clauses for the internal node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeAddClauses( solver * pSat, char * pSop0, char * pSop1, Abc_Obj_t * pNode, Vec_Int_t * vVars )
{
    Abc_Obj_t * pFanin;
    int i, c, nFanins;
    char * pCube;

    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum( pSop0 ) );

    if ( nFanins == 0 )
    {
        vVars->nSize = 0;
        if ( Abc_SopIsConst1(pSop1) )
            Vec_IntPush( vVars, toLit(pNode->Id) );
        else
            Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
    }
 
    // add clauses for the negative phase
    for ( c = 0; ; c++ )
    {
        // get the cube
        pCube = pSop0 + c * (nFanins + 3);
        if ( *pCube == 0 )
            break;
        // add the clause
        vVars->nSize = 0;
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( pCube[i] == '0' )
                Vec_IntPush( vVars, toLit(pFanin->Id) );
            else if ( pCube[i] == '1' )
                Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        }
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }

    // add clauses for the positive phase
    for ( c = 0; ; c++ )
    {
        // get the cube
        pCube = pSop1 + c * (nFanins + 3);
        if ( *pCube == 0 )
            break;
        // add the clause
        vVars->nSize = 0;
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( pCube[i] == '0' )
                Vec_IntPush( vVars, toLit(pFanin->Id) );
            else if ( pCube[i] == '1' )
                Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        }
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds clauses for the PO node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeAddClausesTop( solver * pSat, Abc_Obj_t * pNode, Vec_Int_t * vVars )
{
    Abc_Obj_t * pFanin;

    pFanin = Abc_ObjFanin0(pNode);
    if ( Abc_ObjFaninC0(pNode) )
    {
        vVars->nSize = 0;
        Vec_IntPush( vVars, toLit(pFanin->Id) );
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;

        vVars->nSize = 0;
        Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }
    else
    {
        vVars->nSize = 0;
        Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;

        vVars->nSize = 0;
        Vec_IntPush( vVars, toLit(pFanin->Id) );
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }

    vVars->nSize = 0;
    Vec_IntPush( vVars, toLit(pNode->Id) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


