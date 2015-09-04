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
int Bmc_CollapseExpandCanon( sat_solver * pSat, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit )
{
    int k, n, iLit, status;
    // try removing one literal at a time
    for ( k = Vec_IntSize(vLits) - 1; k >= 0; k-- )
    {
        int Save = Vec_IntEntry( vLits, k );
        if ( Save == -1 )
            continue;
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
int Bmc_CollapseExpand( sat_solver * pSat, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit )
{
    int i, k, iLit, status, nFinal, * pFinal;
    // check against offset
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), nBTLimit, 0, 0, 0 );
    if ( status == l_Undef )
        return -1;
    assert( status == l_False );
    // get subset of literals
    nFinal = sat_solver_final( pSat, &pFinal );
/*
    // collect literals
    Vec_IntClear( vNums );
    for ( i = 0; i < nFinal; i++ )
    {
        iLit = Vec_IntFind( vLits, Abc_LitNot(pFinal[i]) );
        assert( iLit >= 0 );
        Vec_IntPush( vNums, iLit );
    }
*/
    // mark unused literals
    Vec_IntForEachEntry( vLits, iLit, i )
    {
        for ( k = 0; k < nFinal; k++ )
            if ( iLit == Abc_LitNot(pFinal[k]) )
                break;
        if ( k == nFinal )
            Vec_IntWriteEntry( vLits, i, -1 );
    }
    Bmc_CollapseExpandCanon( pSat, vLits, vNums, vTemp, nBTLimit );

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
Vec_Str_t * Bmc_CollapseOneInt( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fVerbose, int fCompl )
{
    int fPrintMinterm = 0;
    int nVars = Gia_ManCiNum(p);
    Vec_Int_t * vVars = Vec_IntAlloc( nVars );
    Vec_Int_t * vLits = Vec_IntAlloc( nVars );
    Vec_Int_t * vNums = Vec_IntAlloc( nVars );
    Vec_Int_t * vCube = Vec_IntAlloc( nVars );
    Vec_Str_t * vSop  = Vec_StrAlloc( 100 );
    int iOut = 0, iLit, iVar, status, n, Count, Start;

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
        {
            Vec_StrPrintStr( vSop, (n ^ fCompl) ? " 1\n" : " 0\n" );
            Vec_StrPush( vSop, '\0' );
            goto cleanup; // const0/1
        }
        status = sat_solver_solve( pSat[n], NULL, NULL, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
        {
            Vec_StrFreeP( &vSop );
            goto cleanup; // timeout
        }
        if ( status == l_False )
        {
            Vec_StrPrintStr( vSop, (n ^ fCompl) ? " 1\n" : " 0\n" );
            Vec_StrPush( vSop, '\0' );
            goto cleanup; // const0/1
        }
    }
    Vec_StrPush( vSop, '\0' );

    // prepare on-set for solving
    if ( fCanon )
        sat_solver_prepare_enum( pSat[0], Vec_IntArray(vVars), Vec_IntSize(vVars) );
    Count = 0;
    while ( 1 )
    {
        // get the assignment
        status = sat_solver_solve( pSat[0], NULL, NULL, 0, 0, 0, 0 );
        if ( status == l_Undef )
        {
            Vec_StrFreeP( &vSop );
            goto cleanup; // timeout
        }
        if ( status == l_False )
            break;
        // check number of cubes
        if ( Count == nCubeLim )
        {
            //printf( "The number of cubes exceeded the limit (%d).\n", nCubeLim );
            Vec_StrFreeP( &vSop );
            goto cleanup; // cube out
        }
        // collect values
        Vec_IntClear( vLits );
        Vec_IntForEachEntry( vVars, iVar, n )
            Vec_IntPush( vLits, Abc_Var2Lit(iVar, !sat_solver_var_value(pSat[0], iVar)) );
        // print minterm
        if ( fPrintMinterm )
        {
            printf( "Mint: " );
            Vec_IntForEachEntry( vLits, iLit, n )
                printf( "%d", !Abc_LitIsCompl(iLit) );
            printf( "\n" );
        }
        // expand the values
        if ( fCanon )
            status = Bmc_CollapseExpandCanon( pSat[1], vLits, vNums, vCube, nBTLimit );
        else
            status = Bmc_CollapseExpand( pSat[1], vLits, vNums, vCube, nBTLimit );
        if ( status < 0 )
        {
            Vec_StrFreeP( &vSop );
            goto cleanup; // timeout
        }
        // collect cube
        Vec_StrPop( vSop );
        Start = Vec_StrSize( vSop );
        Vec_StrFillExtra( vSop, Start + nVars + 4, '-' );
        Vec_StrWriteEntry( vSop, Start + nVars + 0, ' ' );
        Vec_StrWriteEntry( vSop, Start + nVars + 1, (char)(fCompl ? '0' : '1') );
        Vec_StrWriteEntry( vSop, Start + nVars + 2, '\n' );
        Vec_StrWriteEntry( vSop, Start + nVars + 3, '\0' );
        Vec_IntClear( vCube );
        Vec_IntForEachEntry( vNums, iVar, n )
        {
            iLit = Vec_IntEntry( vLits, iVar );
            Vec_IntPush( vCube, Abc_LitNot(iLit) );
            Vec_StrWriteEntry( vSop, Start + iVar, (char)('0' + !Abc_LitIsCompl(iLit)) );
        }
        if ( fVerbose )
            printf( "Cube %4d: %s", Count, Vec_StrArray(vSop) + Start );
        Count++;
        // add cube
        status = sat_solver_addclause( pSat[0], Vec_IntArray(vCube), Vec_IntLimit(vCube) );
        if ( status == 0 )
            break;
    }
    //printf( "Finished enumerating %d assignments.\n", Count );
cleanup:
    Vec_IntFree( vVars );
    Vec_IntFree( vLits );
    Vec_IntFree( vNums );
    Vec_IntFree( vCube );
    sat_solver_delete( pSat[0] );
    sat_solver_delete( pSat[1] );
    Cnf_DataFree( pCnf );
    return vSop;
}
Vec_Str_t * Bmc_CollapseOne( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fVerbose )
{
    Vec_Str_t * vSopOn, * vSopOff;
    int nCubesOn = ABC_INFINITY;
    int nCubesOff = ABC_INFINITY;
    vSopOn = Bmc_CollapseOneInt( p, nCubeLim, nBTLimit, fCanon, fVerbose, 0 );
    if ( vSopOn )
        nCubesOn = Vec_StrCountEntry(vSopOn,'\n');
    Gia_ObjFlipFaninC0( Gia_ManPo(p, 0) );
    vSopOff = Bmc_CollapseOneInt( p, Abc_MinInt(nCubeLim, nCubesOn), nBTLimit, fCanon, fVerbose, 1 );
    Gia_ObjFlipFaninC0( Gia_ManPo(p, 0) );
    if ( vSopOff )
        nCubesOff = Vec_StrCountEntry(vSopOff,'\n');
    if ( vSopOn == NULL )
        return vSopOff;
    if ( vSopOff == NULL )
        return vSopOn;
    if ( nCubesOn <= nCubesOff )
    {
        Vec_StrFree( vSopOff );
        return vSopOn;
    }
    else
    {
        Vec_StrFree( vSopOn );
        return vSopOff;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

