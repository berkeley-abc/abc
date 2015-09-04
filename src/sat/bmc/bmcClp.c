/**CFile****************************************************************

  FileName    [bmcClp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [INT-FX: Interpolation-based logic sharing extraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcClp.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "misc/vec/vecWec.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Cnf_Dat_t * Mf_ManGenerateCnf( Gia_Man_t * pGia, int nLutSize, int fCnfObjIds, int fAddOrCla, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseExpand2( sat_solver * pSat, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit )
{
    int i, Index, status, nFinal, * pFinal;
    // check against offset
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), nBTLimit, 0, 0, 0 );
    if ( status == l_Undef )
        return -1;
    assert( status == l_False );
    // get subset of literals
    nFinal = sat_solver_final( pSat, &pFinal );
    // collect literals
    Vec_IntClear( vNums );
    for ( i = 0; i < nFinal; i++ )
    {
        Index = Vec_IntFind( vLits, Abc_LitNot(pFinal[i]) );
        assert( Index >= 0 );
        Vec_IntPush( vNums, Index );
    }
/*
    int i;
    Vec_IntClear( vNums );
    for ( i = 0; i < Vec_IntSize(vLits); i++ )
        Vec_IntPush( vNums, i );
*/
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseExpand( sat_solver * pSat, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit )
{
    int k, n, iLit, status;
    // try removing one literal at a time
    for ( k = Vec_IntSize(vLits) - 1; k >= 0; k-- )
    {
        int Save = Vec_IntEntry( vLits, k );
        Vec_IntWriteEntry( vLits, k, -1 );
        // put into new array
        Vec_IntClear( vTemp );
        Vec_IntForEachEntry( vLits, iLit, n )
            if ( iLit != -1 )
                Vec_IntPush( vTemp, iLit );
        // check against offset
        status = sat_solver_solve( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return -1;
        if ( status == l_True )
            Vec_IntWriteEntry( vLits, k, Save );
    }
    // put into new array
    Vec_IntClear( vNums );
    Vec_IntForEachEntry( vLits, iLit, n )
        if ( iLit != -1 )
            Vec_IntPush( vNums, n );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseOne( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fVerbose )
{
    int nVars = Gia_ManCiNum(p);
    Vec_Int_t * vVars = Vec_IntAlloc( nVars );
    Vec_Int_t * vLits = Vec_IntAlloc( nVars );
    Vec_Int_t * vNums = Vec_IntAlloc( nVars );
    Vec_Int_t * vCube = Vec_IntAlloc( nVars );
    Vec_Str_t * vStr  = Vec_StrAlloc( nVars+1 );
    int iOut = 0, iLit, iVar, status, n, Count;

    // create SAT solver
    Cnf_Dat_t * pCnf = Mf_ManGenerateCnf( p, 8, 0, 0, 0 );
    sat_solver * pSat[2] = { 
        (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0), 
        (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0) 
    };

    // collect CI variables
    int iCiVarBeg = pCnf->nVars - nVars;// - 1;
    for ( n = 0; n < nVars; n++ )
        Vec_IntPush( vVars, iCiVarBeg + n );

    // check that on-set/off-set is sat
    for ( n = 0; n < 2; n++ )
    {
        iLit = Abc_Var2Lit( iOut + 1, n ); // n=0 => F=1   n=1 => F=0
        status = sat_solver_addclause( pSat[n], &iLit, &iLit + 1 );
        if ( status == 0 )
            return -1; // const0/1
        status = sat_solver_solve( pSat[n], NULL, NULL, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return -3; // timeout
        if ( status == l_False )
            return -1; // const0/1
    }

    // prepare on-set for solving
    sat_solver_prepare_enum( pSat[0], Vec_IntArray(vVars), Vec_IntSize(vVars) );
    for ( Count = 0; Count < nCubeLim; )
    {
        // get the smallest assignment
        status = sat_solver_solve( pSat[0], NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_Undef )
            return -3; // timeout
        if ( status == l_False )
            break;
        // collect values
        Vec_IntClear( vLits );
        Vec_IntForEachEntry( vVars, iVar, n )
            Vec_IntPush( vLits, Abc_Var2Lit(iVar, !sat_solver_var_value(pSat[0], iVar)) );
        // print minterm
//        printf( "Mint: " );
//        Vec_IntForEachEntry( vLits, iLit, n )
//            printf( "%d", !Abc_LitIsCompl(iLit) );
//        printf( "\n" );
        // expand the values
        status = Bmc_CollapseExpand( pSat[1], vLits, vNums, vCube, nBTLimit );
        if ( status < 0 )
            return -3; // timeout
        Count++;
        // print cube
        if ( fVerbose )
        {
            Vec_StrFill( vStr, nVars, '-' );
            Vec_StrPush( vStr, '\0' );
            Vec_IntForEachEntry( vNums, iVar, n )
                Vec_StrWriteEntry( vStr, iVar, (char)('0' + !Abc_LitIsCompl(Vec_IntEntry(vLits, iVar))) );
            printf( "Cube: " );
            printf( "%s\n", Vec_StrArray(vStr) );
        }
        // collect cube
        Vec_IntClear( vCube );
        Vec_IntForEachEntry( vNums, iVar, n )
            Vec_IntPush( vCube, Abc_LitNot(Vec_IntEntry(vLits, iVar)) );
        // add cube
        status = sat_solver_addclause( pSat[0], Vec_IntArray(vCube), Vec_IntLimit(vCube) );
        if ( status == 0 )
            break;
    }
    printf( "Finished enumerating %d assignments.\n", Count );

    // cleanup
    Vec_IntFree( vVars );
    Vec_IntFree( vLits );
    Vec_IntFree( vNums );
    Vec_IntFree( vCube );
    Vec_StrFree( vStr );
    sat_solver_delete( pSat[0] );
    sat_solver_delete( pSat[1] );
    Cnf_DataFree( pCnf );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

