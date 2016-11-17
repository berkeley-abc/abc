/**CFile****************************************************************

  FileName    [sbd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sbd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sbdInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAX_M 12 // max inputs
#define MAX_N 20 // max nodes
#define MAX_K  6 // max lutsize

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Sbd_SolverTopo( int M, int N, int K, int pVars[MAX_N][MAX_M+MAX_N][MAX_K] ) // inputs, nodes, lutsize
{
    sat_solver * pSat = NULL;
    Vec_Int_t * vTemp = Vec_IntAlloc(100);
    // assign vars
    int RetValue, n, i, k, nVars = 0;
    for ( n = 0; n < N; n++ )
    for ( i = 0; i < M+N; i++ )
    for ( k = 0; k < K; k++ )
        pVars[n][i][k] = nVars++;
    printf( "Number of vars = %d.\n", nVars );
    // add constraints
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, nVars );
    // each node is used
    for ( i = 0; i < M+N-1; i++ )
    {
        Vec_IntClear( vTemp );
        for ( n = 0; n < N; n++ )
        for ( k = 0; k < K; k++ )
            Vec_IntPush( vTemp, Abc_Var2Lit(pVars[n][i][k], 0) );
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp) );
        assert( RetValue );
    }
    // each fanin of each node is connected
    for ( n = 0; n < N; n++ )
    for ( k = 0; k < K; k++ )
    {
        Vec_IntClear( vTemp );
        for ( i = 0; i < M+n; i++ )
            Vec_IntPush( vTemp, Abc_Var2Lit(pVars[n][i][k], 0) );
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp) );
        assert( RetValue );
    }
    // each fanin is connected once; fanins are ordered; nodes are ordered
    for ( n = 0; n < N;   n++ )
    for ( i = 0; i < M+N; i++ )
    for ( k = 0; k < K;   k++ )
    {
        int n2, i2, k2;
        for ( n2 = 0; n2 <=n;   n2++ )
        for ( i2 = i; i2 < M+N; i2++ )
        for ( k2 = k; k2 < K;   k2++ )
        {
            if ( n2 == n && i2 == i && k2 == k )
                continue;
            Vec_IntPushTwo( vTemp, Abc_Var2Lit(pVars[n][i][k], 1), Abc_Var2Lit(pVars[n2][i2][k2], 1) );
            RetValue = sat_solver_addclause( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp) );
            assert( RetValue );
        }
    }
    Vec_IntFree( vTemp );
    return pSat;
}
void Sbd_SolverTopoPrint( sat_solver * pSat, int M, int N, int K, int pVars[MAX_N][MAX_M+MAX_N][MAX_K] ) 
{
    int n, i, k;
    printf( "Solution:\n" );
    for ( i = M+N-1; i >= 0; i-- )
    {
        printf( "%2d %c : ", i, i < M ? 'i' : 'n' );
        for ( n = 0; n < N; n++ )
        {
            for ( k = 0; k < K; k++ )
                printf( "%c", sat_solver_var_value(pSat, pVars[n][i][k]) ? '*' : '.' );
            printf( "  " );
        }
        printf( "\n" );
    }
}
void Sbd_SolverTopoTest()
{
    int M = 4; // inputs
    int N = 3; // nodes
    int K = 2; // lutsize
    int status, nCalls, v, nVars;
    int pVars[MAX_N][MAX_M+MAX_N][MAX_K]; // 20 x 32 x 6 = 3840
    Vec_Int_t * vLits = Vec_IntAlloc(100);
    sat_solver * pSat = Sbd_SolverTopo( M, N, K, pVars );
    nVars = sat_solver_nvars( pSat );
    for ( nCalls = 0; nCalls < 1000000; nCalls++ )
    {
        // find onset minterm
        status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_Undef )
            break;
        if ( status == l_False )
            break;
        assert( status == l_True );
        // print solution
        Sbd_SolverTopoPrint( pSat, M, N, K, pVars );
        // remember variable values
        Vec_IntClear( vLits );
        for ( v = 0; v < nVars; v++ )
            if ( sat_solver_var_value(pSat, v) )
                Vec_IntPush( vLits, Abc_Var2Lit(v, 1) );
        // add breaking clause
        status = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits) );
        assert( status );
    }
    printf( "Found %d solutions.\n", nCalls );
    sat_solver_delete( pSat );
    Vec_IntFree( vLits );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

