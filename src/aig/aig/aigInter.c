/**CFile****************************************************************

  FileName    [aigInter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Interpolate two AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigInter.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"
#include "cnf.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int timeCnf;
extern int timeSat;
extern int timeInt;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManInter( Aig_Man_t * pManOn, Aig_Man_t * pManOff, int fVerbose )
{
    void * pSatCnf = NULL;
    Inta_Man_t * pManInter;
    Aig_Man_t * pRes;
    sat_solver * pSat;
    Cnf_Dat_t * pCnfOn, * pCnfOff;
    Vec_Int_t * vVarsAB;
    Aig_Obj_t * pObj, * pObj2;
    int Lits[3], status, i;
    int clk;

    assert( Aig_ManPiNum(pManOn) == Aig_ManPiNum(pManOff) );

clk = clock();
    // derive CNFs
//    pCnfOn  = Cnf_Derive( pManOn, 0 );
//    pCnfOff = Cnf_Derive( pManOff, 0 );
    pCnfOn  = Cnf_DeriveSimple( pManOn, 0 );
    pCnfOff = Cnf_DeriveSimple( pManOff, 0 );
    Cnf_DataLift( pCnfOff, pCnfOn->nVars );
timeCnf += clock() - clk;

clk = clock();
    // start the solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, pCnfOn->nVars + pCnfOff->nVars );

    // add clauses of A
    for ( i = 0; i < pCnfOn->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfOn->pClauses[i], pCnfOn->pClauses[i+1] ) )
        {
            Cnf_DataFree( pCnfOn );
            Cnf_DataFree( pCnfOff );
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    sat_solver_store_mark_clauses_a( pSat );

    // add clauses of B
    for ( i = 0; i < pCnfOff->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfOff->pClauses[i], pCnfOff->pClauses[i+1] ) )
        {
            Cnf_DataFree( pCnfOn );
            Cnf_DataFree( pCnfOff );
            sat_solver_delete( pSat );
            return NULL;
        }
    }

    // add PI clauses
    // collect the common variables
    vVarsAB = Vec_IntAlloc( Aig_ManPiNum(pManOn) );
    Aig_ManForEachPi( pManOn, pObj, i )
    {
        Vec_IntPush( vVarsAB, pCnfOn->pVarNums[pObj->Id] );
        pObj2 = Aig_ManPi( pManOff, i );

        Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObj2->Id], 1 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObj2->Id], 0 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    Cnf_DataFree( pCnfOn );
    Cnf_DataFree( pCnfOff );
    sat_solver_store_mark_roots( pSat );

/*
    status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        Vec_IntFree( vVarsAB );
        Cnf_DataFree( pCnfOn );
        Cnf_DataFree( pCnfOff );
        sat_solver_delete( pSat );
        return NULL;
    }
*/

    // solve the problem
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)0, (sint64)0, (sint64)0, (sint64)0 );
timeSat += clock() - clk;
    if ( status == l_False )
    {
        pSatCnf = sat_solver_store_release( pSat );
//        printf( "unsat\n" );
    }
    else if ( status == l_True )
    {
//        printf( "sat\n" );
    }
    else
    {
//        printf( "undef\n" );
    }
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
    {
        printf( "The SAT problem is not unsat.\n" );
        Vec_IntFree( vVarsAB );
        return NULL;
    }

    // create the resulting manager
clk = clock();
    pManInter = Inta_ManAlloc();
    pRes = Inta_ManInterpolate( pManInter, pSatCnf, vVarsAB, fVerbose );
    Inta_ManFree( pManInter );
timeInt += clock() - clk;
/*
    // test UNSAT core computation
    {
        Intp_Man_t * pManProof;
        Vec_Int_t * vCore;
        pManProof = Intp_ManAlloc();
        vCore = Intp_ManUnsatCore( pManProof, pSatCnf, 0 );
        Intp_ManFree( pManProof );
        Vec_IntFree( vCore );
    }
*/
    Vec_IntFree( vVarsAB );
    Sto_ManFree( pSatCnf );
    return pRes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


