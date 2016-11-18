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
#include "misc/util/utilTruth.h"

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
    int RetValue, n, i, j, k, nVars = 0;
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
        int n2 = n, i2 = i, k2 = k;
        for ( n2 = 0; n2 <= n;   n2++ )
        for ( i2 = i; i2 <  M+N; i2++ )
        for ( k2 = 0; k2 <= k;   k2++ )
        {
            if ( n2 == n && i2 == i && k2 == k )
                continue;
            Vec_IntFillTwo( vTemp, 2, Abc_Var2Lit(pVars[n][i][k], 1), Abc_Var2Lit(pVars[n2][i2][k2], 1) );
            RetValue = sat_solver_addclause( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp) );
            assert( RetValue );
        }
    }
    // exclude fanins of two-input nodes
    if ( K == 2 )
    for ( n = 0; n < N;   n++ )
    for ( i = M; i < M+N; i++ )
    for ( k = 0; k < K;   k++ )
    {
        int k2;
        for ( j = 0;  j < i;  j++ )
        for ( k2 = 0; k2 < K; k2++ )
        {
            Vec_IntClear( vTemp );
            Vec_IntPush( vTemp, Abc_Var2Lit(pVars[n][i][k], 1) );
            Vec_IntPush( vTemp, Abc_Var2Lit(pVars[n][j][!k], 1) );
            Vec_IntPush( vTemp, Abc_Var2Lit(pVars[i-M][j][k2], 1) );
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
    printf( "     | " );
    for ( n = 0; n < N; n++ )
        printf( "%2d  ", M+n );
    printf( "\n" );
    for ( i = M+N-2; i >= 0; i-- )
    {
        printf( "%2d %c | ", i, i < M ? 'i' : ' ' );
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
    int M = 4;  //  6;  // inputs
    int N = 4;  // 16;  // nodes
    int K = 2;  //  2;  // lutsize
    int status, v, nVars, nIter, nSols = 0;
    int pVars[MAX_N][MAX_M+MAX_N][MAX_K]; // 20 x 32 x 6 = 3840
    Vec_Int_t * vLits = Vec_IntAlloc(100);
    sat_solver * pSat = Sbd_SolverTopo( M, N, K, pVars );
    nVars = sat_solver_nvars( pSat );
    for ( nIter = 0; nIter < 1000000; nIter++ )
    {
        // find onset minterm
        status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_Undef )
            break;
        if ( status == l_False )
            break;
        assert( status == l_True );
        nSols++;
        // print solution
        Sbd_SolverTopoPrint( pSat, M, N, K, pVars );
        // remember variable values
        Vec_IntClear( vLits );
        for ( v = 0; v < nVars; v++ )
            if ( sat_solver_var_value(pSat, v) )
                Vec_IntPush( vLits, Abc_Var2Lit(v, 1) );
        // add breaking clause
        status = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits) );
        if ( status == 0 )
            break;
    }
    printf( "Found %d solutions.\n", nSols );
    sat_solver_delete( pSat );
    Vec_IntFree( vLits );
}



/**Function*************************************************************

  Synopsis    [Compute truth table for the given parameter settings.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sbd_SolverTruth( int M, int N, int K, int pLuts[MAX_N][MAX_K], int pValues[MAX_N*((1<<MAX_K)-1)] )
{
    word Truths[MAX_M+MAX_N];
    int i, k, v, nLutPars = (1 << K) - 1;
    assert( M <= 6 );
    assert( N <= MAX_N );
    for ( i = 0; i < M; i++ )
        Truths[i] = s_Truths6[i];
    for ( i = 0; i < N; i++ )
    {
        word Truth = 0, Mint;
        for ( k = 1; k <= nLutPars; k++ )
        {            
            if ( !pValues[i*nLutPars+k-1] )
                continue;
            Mint = ~(word)0;
            for ( v = 0; v < K; v++ )
                Mint &= ((k >> v) & 1) ? Truths[pLuts[i][v]] :  ~Truths[pLuts[i][v]];
            Truth |= Mint;
        }
        Truths[M+i] = Truth;
    }
    return Truths[M+N-1];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbd_SolverFunc( int M, int N, int K, int pLuts[MAX_N][MAX_K], word TruthInit, int * pValues ) 
{
    int fVerbose = 0;
    sat_solver * pSat = NULL;
    int pLits[MAX_K+2], pLits2[MAX_K+2], nLits;
    int nLutPars = (1 << K) - 1, nVars = N * nLutPars;
    int i, k, m, status, iMint, Iter, fCompl = (int)(TruthInit & 1);
    word TruthNew, Truth = (TruthInit & 1) ? ~TruthInit : TruthInit;
    word Mask = M < 6 ? Abc_Tt6Mask(1 << M) : ~(word)0;
    printf( "Number of parameters %d x %d = %d.\n", N, nLutPars, nVars );
    // create solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, nVars );
    // start with the last minterm
    iMint = (1 << M) - 1;
    for ( Iter = 0; Iter < (1 << M); Iter++ )
    {
        // assign the first intermediate variable
        int nVarStart = sat_solver_nvars(pSat);
        sat_solver_setnvars( pSat, nVarStart + N - 1 );

        // add clauses for nodes
        if ( fVerbose )
            printf( "\nIter %3d : Minterm %d\n", Iter, iMint );
        for ( i = 0; i < N; i++ )
        for ( m = 0; m <= nLutPars; m++ )
        {
            if ( fVerbose )
                printf( "i = %d.  m = %d.\n", i, m );
            // selector variables
            nLits = 0;
            for ( k = 0; k < K; k++ ) 
            {
                if ( pLuts[i][k] >= M )
                {
                    assert( pLuts[i][k] - M < N - 1 );
                    pLits[nLits] = pLits2[nLits] = Abc_Var2Lit( nVarStart + pLuts[i][k] - M, (m >> k) & 1 ); 
                    nLits++;
                }
                else if ( ((iMint >> pLuts[i][k]) & 1) != ((m >> k) & 1) )
                    break;
            }
            if ( k < K )
                continue;
            // add parameter
            if ( m )
            {
                pLits[nLits]  = Abc_Var2Lit( i*nLutPars + m-1, 1 );
                pLits2[nLits] = Abc_Var2Lit( i*nLutPars + m-1, 0 );
                nLits++;
            }
            // node variable
            if ( i != N - 1 ) 
            {
                pLits[nLits]  = Abc_Var2Lit( nVarStart + i, 0 );
                pLits2[nLits] = Abc_Var2Lit( nVarStart + i, 1 );
                nLits++;
            }
            // add clauses
            if ( i != N - 1 || ((TruthInit >> iMint) & 1) != fCompl )
            {
                status = sat_solver_addclause( pSat, pLits2, pLits2 + nLits );
                if ( status == 0 )
                {
                    fCompl = -1;
                    goto finish;
                }
            }
            if ( (i != N - 1 || ((TruthInit >> iMint) & 1) == fCompl) && m > 0 )
            {
                status = sat_solver_addclause( pSat, pLits, pLits + nLits );
                if ( status == 0 )
                {
                    fCompl = -1;
                    goto finish;
                }
            }
        }

        // run SAT solver
        status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_Undef )
            break;
        if ( status == l_False )
        {
            fCompl = -1;
            goto finish;
        }
        assert( status == l_True );

        // collect values
        for ( i = 0; i < nVars; i++ )
            pValues[i] = sat_solver_var_value(pSat, i);
        TruthNew = Sbd_SolverTruth( M, N, K, pLuts, pValues );
        if ( fVerbose )
        {
            for ( i = 0; i < nVars; i++ )
                printf( "%d=%d ", i, pValues[i] );
            printf( "  " );
            for ( i = nVars; i < sat_solver_nvars(pSat); i++ )
                printf( "%d=%d ", i, sat_solver_var_value(pSat, i) );
            printf( "\n" );
            Extra_PrintBinary( stdout, (unsigned *)&Truth, (1 << M) );    printf( "\n" );
            Extra_PrintBinary( stdout, (unsigned *)&TruthNew, (1 << M) ); printf( "\n" );
        }
        if ( (Truth & Mask) == (Mask & TruthNew) )
            break;

        // get new minterm
        iMint = Abc_Tt6FirstBit( Truth ^ TruthNew );
    }
finish:
    printf( "Finished after %d iterations and %d conflicts.\n", Iter, sat_solver_nconflicts(pSat) );
    sat_solver_delete( pSat );
    return fCompl;
}
void Sbd_SolverFuncTest() 
{
//    int M = 4;  //  6;  // inputs
//    int N = 3;  // 16;  // nodes
//    int K = 2;  //  2;  // lutsize
    int M = 6;  //  6;  // inputs
    int N = 5;  // 16;  // nodes
    int K = 2;  //  2;  // lutsize
//    word Truth = ~(word)(1 << 0);
    word Truth = ~(word)(23423);
    int pLuts[MAX_N][MAX_K] = { {0,1}, {2,3}, {4,5}, {6,7}, {8,9} };
    int pValues[MAX_N*((1<<MAX_K)-1)];
    int i, k, nLutPars = (1 << K) - 1;
    int Res = Sbd_SolverFunc( M, N, K, pLuts, Truth, pValues );
    if ( Res == -1 )
    {
        printf( "Solution does not exist.\n" );
        return;
    }
    printf( "Result (compl = %d):\n", Res );
    for ( i = 0; i < N; i++ )
    {
        for ( k = nLutPars-1; k >= 0; k-- )
            printf( "%d", pValues[i*nLutPars+k] );
        printf( "0\n" );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

