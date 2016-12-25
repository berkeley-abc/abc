/**CFile****************************************************************

  FileName    [sbdLut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [CNF computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sbdLut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sbdInt.h"

ABC_NAMESPACE_IMPL_START

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
// count the number of parameter variables in the structure
int Sbd_ProblemCountParams( int nStrs, Sbd_Str_t * pStr0 )
{
    Sbd_Str_t * pStr;  int nPars = 0;
    for ( pStr = pStr0; pStr < pStr0 + nStrs; pStr++ )
        nPars += (pStr->fLut ? 1 << pStr->nVarIns : pStr->nVarIns);
    return nPars;
}
// add clauses for the structure
void Sbd_ProblemAddClauses( sat_solver * pSat, int nVars, int nStrs, int * pVars, Sbd_Str_t * pStr0 )
{   
    // variable order:  inputs, structure outputs, parameters
    Sbd_Str_t * pStr;
    int VarOut = nVars;
    int VarPar = nVars + nStrs;
    int m, k, n, status, pLits[SBD_SIZE_MAX+2];
    for ( pStr = pStr0; pStr < pStr0 + nStrs; pStr++, VarOut++ )
    {
        if ( pStr->fLut )
        {
            int nMints = 1 << pStr->nVarIns;
            assert( pStr->nVarIns <= 6 );
            for ( m = 0; m < nMints; m++, VarPar++ )
            {
                for ( k = 0; k < pStr->nVarIns; k++ )
                    pLits[k] = Abc_Var2Lit( pVars[pStr->VarIns[k]], (m >> k) & 1 ); 
                for ( n = 0; n < 2; n++ )
                {
                    pLits[pStr->nVarIns]   = Abc_Var2Lit( pVars[VarPar], n );
                    pLits[pStr->nVarIns+1] = Abc_Var2Lit( pVars[VarOut], !n );
                    status = sat_solver_addclause( pSat, pLits, pLits + pStr->nVarIns + 2 );
                    assert( status );
                }
            }
        }
        else
        {
            for ( k = 0; k < pStr->nVarIns; k++, VarPar++ )
            {
                for ( n = 0; n < 2; n++ )
                {
                    pLits[0] = Abc_Var2Lit( pVars[VarPar], 1 );
                    pLits[1] = Abc_Var2Lit( pVars[VarOut], n );
                    pLits[2] = Abc_Var2Lit( pVars[pStr->VarIns[k]], !n );
                    status = sat_solver_addclause( pSat, pLits, pLits + 3 );
                    assert( status );
                }
            }
        }
    }
}
void Sbd_ProblemAddClausesInit( sat_solver * pSat, int nVars, int nStrs, int * pVars, Sbd_Str_t * pStr0 )
{
    Sbd_Str_t * pStr;
    int VarPar = nVars + nStrs;
    int m, m2, pLits[2], status;
    // make sure selector parameters are mutually exclusive
    for ( pStr = pStr0; pStr < pStr0 + nStrs; pStr++, VarPar = pStr->fLut ? 1 << pStr->nVarIns : pStr->nVarIns )
    {
        if ( pStr->fLut )
            continue;
        for ( m = 0; m < pStr->nVarIns; m++ )
        for ( m2 = m+1; m2 < pStr->nVarIns; m2++ )
        {
            pLits[0] = Abc_Var2Lit( pVars[VarPar + m], 1 );
            pLits[1] = Abc_Var2Lit( pVars[VarPar + m2], 1 );
            status = sat_solver_addclause( pSat, pLits, pLits + 2 );
            assert( status );
        }
    }
}
void Sbd_ProblemPrintSolution( int nStrs, Sbd_Str_t * pStr0, Vec_Int_t * vLits )
{
    Sbd_Str_t * pStr;
    int m, nIters, iLit = 0;
    printf( "Solution found:\n" );
    for ( pStr = pStr0; pStr < pStr0 + nStrs; pStr++ )
    {
        nIters = pStr->fLut ? 1 << pStr->nVarIns : pStr->nVarIns;
        printf( "%s%d : ", pStr->fLut ? "LUT":"SEL", pStr-pStr0 );
        for ( m = 0; m < nIters; m++ )
            printf( "%d", Abc_LitIsCompl(Vec_IntEntry(vLits, iLit++)) );
        printf( "\n" );
    }
    assert( iLit == Vec_IntSize(vLits) );
}
void Sbd_ProblemCollectSolution( int nStrs, Sbd_Str_t * pStr0, Vec_Int_t * vLits, word Truths[SBD_LUTS_MAX] )
{
}

/**Function*************************************************************

  Synopsis    [Solves QBF problem for the given window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbd_ProblemSolve( Gia_Man_t * p, Vec_Int_t * vMirrors, 
                       int Pivot, Vec_Int_t * vWinObjs, Vec_Int_t * vObj2Var, 
                       Vec_Int_t * vTfo, Vec_Int_t * vRoots, 
                       Vec_Int_t * vDivSet, int nStrs, Sbd_Str_t * pStr0, word Truths[SBD_LUTS_MAX] )  // divisors, structures
{
    extern sat_solver * Sbd_ManSatSolver( sat_solver * pSat, Gia_Man_t * p, Vec_Int_t * vMirrors, int Pivot, Vec_Int_t * vWinObjs, Vec_Int_t * vObj2Var, Vec_Int_t * vTfo, Vec_Int_t * vRoots, int fQbf );
    
    Vec_Int_t * vLits    = Vec_IntAlloc( 100 );
    sat_solver * pSatCec = Sbd_ManSatSolver( NULL, p, vMirrors, Pivot, vWinObjs, vObj2Var, vTfo, vRoots, 1 );
    sat_solver * pSatQbf = sat_solver_new();

    int nVars      = Vec_IntSize( vDivSet );
    int nPars      = Sbd_ProblemCountParams( nStrs, pStr0 );

    int VarCecOut  = Vec_IntSize(vWinObjs) + Vec_IntSize(vTfo) + Vec_IntSize(vRoots);
    int VarCecPar  = VarCecOut + 1;
    int VarCecFree = VarCecPar + nPars;

    int VarQbfPar  = 0;
    int VarQbfFree = nPars;

    int pVarsCec[256];
    int pVarsQbf[256];
    int i, iVar, iLit;
    int RetValue = 0;

    assert( Vec_IntSize(vDivSet) <= SBD_SIZE_MAX );
    assert( nVars + nStrs + nPars <= 256 );

    // collect CEC variables
    Vec_IntForEachEntry( vDivSet, iVar, i )
        pVarsCec[i] = iVar;
    pVarsCec[nVars] = VarCecOut;
    for ( i = 1; i < nStrs; i++ )
        pVarsCec[nVars + i] = VarCecFree++;
    for ( i = 0; i < nPars; i++ )
        pVarsCec[nVars + nStrs + i] = VarCecPar + i;

    // collect QBF variables
    for ( i = 0; i < nVars + nStrs; i++ )
        pVarsQbf[i] = -1;
    for ( i = 0; i < nPars; i++ )
        pVarsQbf[nVars + nStrs + i] = VarQbfPar + i;

    // add clauses to the CEC problem
    Sbd_ProblemAddClauses( pSatCec, nVars, nStrs, pVarsCec, pStr0 );

    // create QBF solver
    sat_solver_setnvars( pSatQbf, 1000 );
    Sbd_ProblemAddClausesInit( pSatQbf, nVars, nStrs, pVarsQbf, pStr0 );

    // assume all parameter variables are 0
    Vec_IntClear( vLits );
    for ( i = 0; i < nPars; i++ )
        Vec_IntPush( vLits, Abc_Var2Lit(VarCecPar + i, 1) );
    while ( 1 )
    {
        // check if these parameters solve the problem
        int status = sat_solver_solve( pSatCec, Vec_IntArray(vLits), Vec_IntLimit(vLits), 0, 0, 0, 0 );
        if ( status == l_False ) // solution found
            break;
        assert( status == l_True );
        Vec_IntClear( vLits );
        // create new QBF variables
        for ( i = 0; i < nVars + nStrs; i++ )
            pVarsQbf[i] = VarQbfFree++;
        // set their values
        Vec_IntForEachEntry( vDivSet, iVar, i )
        {
            iLit = Abc_Var2Lit( pVarsQbf[i], sat_solver_var_value(pSatCec, iVar) );
            status = sat_solver_addclause( pSatQbf, &iLit, &iLit + 1 );
            assert( status );
        }
        iLit = Abc_Var2Lit( pVarsQbf[nVars], sat_solver_var_value(pSatCec, VarCecOut) );
        status = sat_solver_addclause( pSatQbf, &iLit, &iLit + 1 );
        assert( status );
        // add clauses to the QBF problem
        Sbd_ProblemAddClauses( pSatQbf, nVars, nStrs, pVarsQbf, pStr0 );
        // check if solution still exists
        status = sat_solver_solve( pSatQbf, NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_False ) // solution does not exist
            break;
        assert( status == l_True ); 
        // find the new values of parameters
        assert( Vec_IntSize(vLits) == 0 );
        for ( i = 0; i < nPars; i++ )
            Vec_IntPush( vLits, Abc_Var2Lit(VarCecPar + i, sat_solver_var_value(pSatQbf, VarQbfPar + i)) );
    }
    if ( Vec_IntSize(vLits) > 0 )
    {
        Sbd_ProblemPrintSolution( nStrs, pStr0, vLits );
        Sbd_ProblemCollectSolution( nStrs, pStr0, vLits, Truths );
        RetValue = 1;
    }
    else 
        printf( "Solution does not exist.\n" );

    sat_solver_delete( pSatCec );
    sat_solver_delete( pSatQbf );
    Vec_IntFree( vLits );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

