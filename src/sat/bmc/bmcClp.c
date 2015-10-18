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

// enumerate cubes and literals
#define Bmc_SopForEachCube( pSop, nVars, pCube )                        \
    for ( pCube = (pSop); *pCube; pCube += (nVars) + 3 )

/**Function*************************************************************

  Synopsis    [Perform approximate irredundant step on the cover.]

  Description [Iterate through the cubes in the reverse order and
  check if each cube is contained in the previously seen cubes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseIrredundant( Vec_Str_t * vSop, int nCubes, int nVars )
{
    int nBTLimit = 0;
    sat_solver * pSat; 
    int i, k, status, iLit, nRemoved = 0; 
    Vec_Int_t * vLits = Vec_IntAlloc(nVars);
    // collect cubes
    char * pCube, * pSop = Vec_StrArray(vSop);
    Vec_Ptr_t * vCubes = Vec_PtrAlloc(nCubes);
    assert( Vec_StrSize(vSop) == nCubes * (nVars + 3) + 1 );
    Bmc_SopForEachCube( pSop, nVars, pCube )
        Vec_PtrPush( vCubes, pCube );
    // create SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, nVars );
    // iterate through cubes in the reverse order
    Vec_PtrForEachEntryReverse( char *, vCubes, pCube, i )
    {
        // collect literals
        Vec_IntClear( vLits );
        for ( k = 0; k < nVars; k++ )
            if ( pCube[k] != '-' )
                Vec_IntPush( vLits, Abc_Var2Lit(k, pCube[k] == '1') );
        // check if this cube intersects with the complement of other cubes in the solver
        // if it does not intersect, then it is redundant and can be skipped
        // if it does, then it should be added
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef ) // timeout
            break;
        if ( status == l_False ) // unsat
        {
            Vec_PtrWriteEntry( vCubes, i, NULL );
            nRemoved++;
            continue;
        }
        assert( status == l_True );
        // make a clause out of the cube by complementing its literals
        Vec_IntForEachEntry( vLits, iLit, k )
            Vec_IntWriteEntry( vLits, k, Abc_LitNot(iLit) );
        // add it to the solver
        status = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits) );
        assert( status == 1 );
    }
    //printf( "Approximate irrendundant reduced %d cubes (out of %d).\n", nRemoved, nCubes );
    // cleanup cover
    if ( i == -1 && nRemoved > 0 ) // finished without timeout and removed some cubes
    {
        int j = 0;
        Vec_PtrForEachEntry( char *, vCubes, pCube, i )
            if ( pCube != NULL )
                for ( k = 0; k < nVars + 3; k++ )
                    Vec_StrWriteEntry( vSop, j++, pCube[k] );
        Vec_StrWriteEntry( vSop, j++, '\0' );
        Vec_StrShrink( vSop, j );
    }
    sat_solver_delete( pSat );
    Vec_PtrFree( vCubes );
    Vec_IntFree( vLits );
    return i == -1 ? 1 : 0;
}

/**Function*************************************************************

  Synopsis    [Performs one round of removing literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseExpandRound( sat_solver * pSat, sat_solver * pSatOn, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit, int fCanon )
{
    int k, n, iLit, status;
    // try removing one literal at a time
    for ( k = Vec_IntSize(vLits) - 1; k >= 0; k-- )
    {
        int Save = Vec_IntEntry( vLits, k );
        if ( Save == -1 )
            continue;
        // check if this literal when expanded overlaps with the on-set
        if ( pSatOn )
        {
            // it is ok to skip the first round if the literal is positive
            if ( fCanon && !Abc_LitIsCompl(Save) )
                continue;
            // put into new array
            Vec_IntClear( vTemp );
            Vec_IntForEachEntry( vLits, iLit, n )
                if ( iLit != -1 )
                    Vec_IntPush( vTemp, Abc_LitNotCond(iLit, k==n) );
            // check against onset
            status = sat_solver_solve( pSatOn, Vec_IntArray(vTemp), Vec_IntLimit(vTemp), nBTLimit, 0, 0, 0 );
            if ( status == l_Undef )
                return -1;
            //printf( "%d", status == l_True );
            if ( status == l_False )
                continue;
            // otherwise keep trying to remove it
        }
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
//    if ( pSatOn )
//    printf( "\n" );
    // put into new array
    Vec_IntClear( vNums );
    Vec_IntForEachEntry( vLits, iLit, n )
        if ( iLit != -1 )
            Vec_IntPush( vNums, n );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Expends minterm into a cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_CollapseExpand( sat_solver * pSat, sat_solver * pSatOn, Vec_Int_t * vLits, Vec_Int_t * vNums, Vec_Int_t * vTemp, int nBTLimit, int fCanon )
{
    // perform one quick reduction if it is non-canonical
    if ( !fCanon )
    {
        int i, k, iLit, status, nFinal, * pFinal;
        // check against offset
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return -1;
        assert( status == l_False );
        // get subset of literals
        nFinal = sat_solver_final( pSat, &pFinal );
        // mark unused literals
        Vec_IntForEachEntry( vLits, iLit, i )
        {
            for ( k = 0; k < nFinal; k++ )
                if ( iLit == Abc_LitNot(pFinal[k]) )
                    break;
            if ( k == nFinal )
                Vec_IntWriteEntry( vLits, i, -1 );
        }
    }
    Bmc_CollapseExpandRound( pSat, pSatOn, vLits, vNums, vTemp, nBTLimit, fCanon );
    Bmc_CollapseExpandRound( pSat, NULL,   vLits, vNums, vTemp, nBTLimit, fCanon );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns SAT solver in the 'sat' state with the given assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_ComputeCanonical( sat_solver * pSat, Vec_Int_t * vLits, Vec_Int_t * vTemp, int nBTLimit )
{
    int i, k, iLit, status = l_Undef;
    for ( i = 0; i < Vec_IntSize(vLits); i++ )
    {
        // copy the first i+1 literals
        Vec_IntClear( vTemp );
        Vec_IntForEachEntryStop( vLits, iLit, k, i+1 )
            Vec_IntPush( vTemp, iLit );
        // check if it satisfies the on-set
        status = sat_solver_solve( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return l_Undef;
        if ( status == l_True )
            continue;
        // if it is UNSAT, try the opposite literal
        iLit = Vec_IntEntry( vLits, i );
        // if literal is positive, there is no way to flip it
        if ( !Abc_LitIsCompl(iLit) )
            return l_False;
        Vec_IntWriteEntry( vLits, i, Abc_LitNot(iLit) );
        Vec_IntForEachEntryStart( vLits, iLit, k, i+1 )
            Vec_IntWriteEntry( vLits, k, Abc_LitNot(Abc_LitRegular(iLit)) );
        // recheck
        i--;
    }
    assert( status == l_True );
    return status;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Bmc_CollapseOneInt( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fReverse, int fVerbose, int fCompl )
{
    int fPrintMinterm = 0;
    int nVars = Gia_ManCiNum(p);
    Vec_Int_t * vVars = Vec_IntAlloc( nVars );
    Vec_Int_t * vLits = Vec_IntAlloc( nVars );
    Vec_Int_t * vLitsC= Vec_IntAlloc( nVars );
    Vec_Int_t * vNums = Vec_IntAlloc( nVars );
    Vec_Int_t * vCube = Vec_IntAlloc( nVars );
    Vec_Str_t * vSop  = Vec_StrAlloc( 100 );
    int iOut = 0, iLit, iVar, status, n, Count, Start;

    // create SAT solver
    Cnf_Dat_t * pCnf = Mf_ManGenerateCnf( p, 8, 0, 0, 0 );
    sat_solver * pSat[3] = { 
        (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0), 
        (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0),
        fCanon ? (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0) : NULL
    };

    // collect CI variables
    int iCiVarBeg = pCnf->nVars - nVars;// - 1;
    if ( fReverse )
        for ( n = nVars - 1; n >= 0; n-- )
            Vec_IntPush( vVars, iCiVarBeg + n );
    else
        for ( n = 0; n < nVars; n++ )
            Vec_IntPush( vVars, iCiVarBeg + n );

    // start with all negative literals
    Vec_IntForEachEntry( vVars, iVar, n )
        Vec_IntPush( vLitsC, Abc_Var2Lit(iVar, 1) );

    // check that on-set/off-set is sat
    for ( n = 0; n < 2 + fCanon; n++ )
    {
        iLit = Abc_Var2Lit( iOut + 1, n&1 ); // n=0 => F=1   n=1 => F=0
        status = sat_solver_addclause( pSat[n], &iLit, &iLit + 1 );
        if ( status == 0 )
        {
            Vec_StrPrintStr( vSop, ((n&1) ^ fCompl) ? " 1\n" : " 0\n" );
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
            Vec_StrPrintStr( vSop, ((n&1) ^ fCompl) ? " 1\n" : " 0\n" );
            Vec_StrPush( vSop, '\0' );
            goto cleanup; // const0/1
        }
    }
    Vec_StrPush( vSop, '\0' );

    // prepare on-set for solving
//    if ( fCanon )
//        sat_solver_prepare_enum( pSat[0], Vec_IntArray(vVars), Vec_IntSize(vVars) );
    Count = 0;
    while ( 1 )
    {
        // get the assignment
        if ( fCanon )
            status = Bmc_ComputeCanonical( pSat[0], vLitsC, vCube, nBTLimit );
        else
        {
            sat_solver_clean_polarity( pSat[0], Vec_IntArray(vVars), Vec_IntSize(vVars) );
            status = sat_solver_solve( pSat[0], NULL, NULL, 0, 0, 0, 0 );
        }
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
        Vec_IntClear( vLitsC );
        Vec_IntForEachEntry( vVars, iVar, n )
        {
            iLit = Abc_Var2Lit(iVar, !sat_solver_var_value(pSat[0], iVar));
            Vec_IntPush( vLits, iLit );
            Vec_IntPush( vLitsC, iLit );
        }
        // print minterm
        if ( fPrintMinterm )
        {
            printf( "Mint: " );
            Vec_IntForEachEntry( vLits, iLit, n )
                printf( "%d", !Abc_LitIsCompl(iLit) );
            printf( "\n" );
        }
        // expand the values
        status = Bmc_CollapseExpand( pSat[1], fCanon ? pSat[2] : pSat[0], vLits, vNums, vCube, nBTLimit, fCanon );
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
            if ( fReverse )
                Vec_StrWriteEntry( vSop, Start + nVars - iVar - 1, (char)('0' + !Abc_LitIsCompl(iLit)) );
            else 
                Vec_StrWriteEntry( vSop, Start + iVar, (char)('0' + !Abc_LitIsCompl(iLit)) );
        }
        if ( fVerbose )
            printf( "Cube %4d: %s", Count, Vec_StrArray(vSop) + Start );
        Count++;
        // add cube
        status = sat_solver_addclause( pSat[0], Vec_IntArray(vCube), Vec_IntLimit(vCube) );
        if ( status == 0 )
            break;
        // add cube
        if ( fCanon )
            status = sat_solver_addclause( pSat[2], Vec_IntArray(vCube), Vec_IntLimit(vCube) );
        assert( status == 1 );
    }
    //printf( "Finished enumerating %d assignments.\n", Count );
cleanup:
    Vec_IntFree( vVars );
    Vec_IntFree( vLits );
    Vec_IntFree( vLitsC );
    Vec_IntFree( vNums );
    Vec_IntFree( vCube );
    sat_solver_delete( pSat[0] );
    sat_solver_delete( pSat[1] );
    if ( fCanon )
    sat_solver_delete( pSat[2] );
    Cnf_DataFree( pCnf );
    // quickly reduce contained cubes
    if ( vSop != NULL )
        Bmc_CollapseIrredundant( vSop, Vec_StrSize(vSop)/(nVars +3), nVars );
    return vSop;
}
Vec_Str_t * Bmc_CollapseOne2( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fReverse, int fVerbose )
{
    Vec_Str_t * vSopOn, * vSopOff;
    int nCubesOn = ABC_INFINITY;
    int nCubesOff = ABC_INFINITY;
    vSopOn = Bmc_CollapseOneInt( p, nCubeLim, nBTLimit, fCanon, fReverse, fVerbose, 0 );
    if ( vSopOn )
        nCubesOn = Vec_StrCountEntry(vSopOn,'\n');
    Gia_ObjFlipFaninC0( Gia_ManPo(p, 0) );
    vSopOff = Bmc_CollapseOneInt( p, Abc_MinInt(nCubeLim, nCubesOn), nBTLimit, fCanon, fReverse, fVerbose, 1 );
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


/**Function*************************************************************

  Synopsis    [This code computes on-set and off-set simultaneously.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Bmc_CollapseOne( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fReverse, int fVerbose )
{
    int fVeryVerbose = fVerbose;
    int nVars = Gia_ManCiNum(p);
    Cnf_Dat_t * pCnf = Mf_ManGenerateCnf( p, 8, 0, 0, 0 );
    sat_solver * pSat[2]      = { (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0), (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0) };
    sat_solver * pSatClean[2] = { (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0), (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0) };
    Vec_Str_t * vSop[2]   = { Vec_StrAlloc(1000),  Vec_StrAlloc(1000)  }, * vRes = NULL;
    Vec_Int_t * vLitsC[2] = { Vec_IntAlloc(nVars), Vec_IntAlloc(nVars) };
    Vec_Int_t * vVars = Vec_IntAlloc( nVars );
    Vec_Int_t * vLits = Vec_IntAlloc( nVars );
    Vec_Int_t * vNums = Vec_IntAlloc( nVars );
    Vec_Int_t * vCube = Vec_IntAlloc( nVars );
    int n, v, iVar, iLit, iCiVarBeg, iCube, Start, status;
    abctime clk = 0, Time[2][2] = {{0}};
    int fComplete[2] = {0};

    // collect CI variables
    iCiVarBeg = pCnf->nVars - nVars;// - 1;
    if ( fReverse )
        for ( v = nVars - 1; v >= 0; v-- )
            Vec_IntPush( vVars, iCiVarBeg + v );
    else
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vVars, iCiVarBeg + v );

    // check that on-set/off-set is sat
    for ( n = 0; n < 2; n++ )
    {
        iLit = Abc_Var2Lit( 1, n ); // n=0 => F=1   n=1 => F=0
        status = sat_solver_solve( pSat[n], &iLit, &iLit + 1, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            goto cleanup; // timeout
        if ( status == l_False )
        {
            Vec_StrPrintStr( vSop[0], n ? " 1\n\0" : " 0\n\0" );
            fComplete[0] = 1;
            goto cleanup; // const0/1
        }
        // start with all negative literals
        Vec_IntForEachEntry( vVars, iVar, v )
            Vec_IntPush( vLitsC[n], Abc_Var2Lit(iVar, 1) );
        // add literals to the solver
        status = sat_solver_addclause( pSat[n], &iLit, &iLit + 1 );
        assert( status );
        status = sat_solver_addclause( pSatClean[n], &iLit, &iLit + 1 );
        assert( status );
        // start cover
        Vec_StrPush( vSop[n], '\0' );
    }

    // compute cube pairs
    for ( iCube = 0; iCube < nCubeLim; iCube++ )
    {
        for ( n = 0; n < 2; n++ )
        {
            if ( fVeryVerbose ) clk = Abc_Clock();
            // get the assignment
            if ( fCanon )
                status = Bmc_ComputeCanonical( pSat[n], vLitsC[n], vCube, nBTLimit );
            else
            {
                sat_solver_clean_polarity( pSat[n], Vec_IntArray(vVars), Vec_IntSize(vVars) );
                status = sat_solver_solve( pSat[n], NULL, NULL, 0, 0, 0, 0 );
            }
            if ( fVeryVerbose ) Time[n][0] += Abc_Clock() - clk;
            if ( status == l_Undef )
                goto cleanup; // timeout
            if ( status == l_False )
            {
                fComplete[n] = 1;
                break;
            }
            // collect values
            Vec_IntClear( vLits );
            Vec_IntClear( vLitsC[n] );
            Vec_IntForEachEntry( vVars, iVar, v )
            {
                iLit = Abc_Var2Lit(iVar, !sat_solver_var_value(pSat[n], iVar));
                Vec_IntPush( vLits, iLit );
                Vec_IntPush( vLitsC[n], iLit );
            }
            // expand the values
            if ( fVeryVerbose ) clk = Abc_Clock();
            status = Bmc_CollapseExpand( pSatClean[!n], pSat[n], vLits, vNums, vCube, nBTLimit, fCanon );
            if ( fVeryVerbose ) Time[n][1] += Abc_Clock() - clk;
            if ( status < 0 )
                goto cleanup; // timeout
            // collect cube
            Vec_StrPop( vSop[n] );
            Start = Vec_StrSize( vSop[n] );
            Vec_StrFillExtra( vSop[n], Start + nVars + 4, '-' );
            Vec_StrWriteEntry( vSop[n], Start + nVars + 0, ' ' );
            Vec_StrWriteEntry( vSop[n], Start + nVars + 1, (char)(n ? '0' : '1') );
            Vec_StrWriteEntry( vSop[n], Start + nVars + 2, '\n' );
            Vec_StrWriteEntry( vSop[n], Start + nVars + 3, '\0' );
            Vec_IntClear( vCube );
            Vec_IntForEachEntry( vNums, iVar, v )
            {
                iLit = Vec_IntEntry( vLits, iVar );
                Vec_IntPush( vCube, Abc_LitNot(iLit) );
                if ( fReverse )
                    Vec_StrWriteEntry( vSop[n], Start + nVars - iVar - 1, (char)('0' + !Abc_LitIsCompl(iLit)) );
                else 
                    Vec_StrWriteEntry( vSop[n], Start + iVar, (char)('0' + !Abc_LitIsCompl(iLit)) );
            }
            // add cube
            status = sat_solver_addclause( pSat[n], Vec_IntArray(vCube), Vec_IntLimit(vCube) );
            if ( status == 0 )
            {
                fComplete[n] = 1;
                break;
            }
            assert( status == 1 );
        }
        if ( fComplete[0] || fComplete[1] )
            break;
    }
cleanup:
    Vec_IntFree( vVars );
    Vec_IntFree( vLits );
    Vec_IntFree( vLitsC[0] );
    Vec_IntFree( vLitsC[1] );
    Vec_IntFree( vNums );
    Vec_IntFree( vCube );
    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat[0] );
    sat_solver_delete( pSat[1] );
    sat_solver_delete( pSatClean[0] );
    sat_solver_delete( pSatClean[1] );
    assert( !fComplete[0] || !fComplete[1] );
    if ( fComplete[0] || fComplete[1] ) // one of the cover is computed
    {
        vRes = vSop[fComplete[1]]; vSop[fComplete[1]] = NULL;
        Bmc_CollapseIrredundant( vRes, Vec_StrSize(vRes)/(nVars +3), nVars );
        if ( fVeryVerbose )
        {
            printf( "Processed output with %d supp vars and %d cubes.\n", nVars, Vec_StrSize(vRes)/(nVars +3) );
            Abc_PrintTime( 1, "Onset  minterm", Time[0][0] );
            Abc_PrintTime( 1, "Onset  expand ", Time[0][1] );
            Abc_PrintTime( 1, "Offset minterm", Time[1][0] );
            Abc_PrintTime( 1, "Offset expand ", Time[1][1] );
        }
    }
    Vec_StrFreeP( &vSop[0] );
    Vec_StrFreeP( &vSop[1] );
    return vRes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

