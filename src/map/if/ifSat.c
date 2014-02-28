/**CFile****************************************************************

  FileName    [ifSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [SAT-based evaluation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifSat.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Builds SAT instance for the given structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * If_ManSatBuildXY( int nLutSize )
{
    int nMintsL = (1 << nLutSize);
    int nMintsF = (1 << (2 * nLutSize - 1));
    int nVars   = 2 * nMintsL + nMintsF;
    int iVarP0  = 0;           // LUT0 parameters (total nMintsL)
    int iVarP1  = nMintsL;     // LUT1 parameters (total nMintsL)
    int m,iVarM = 2 * nMintsL; // MUX vars        (total nMintsF)
    sat_solver * p = sat_solver_new();
    sat_solver_setnvars( p, nVars );
    for ( m = 0; m < nMintsF; m++ )
        sat_solver_add_mux( p, iVarP0 + m % nMintsL, iVarP1 + 2 * (m / nMintsL) + 1, iVarP1 + 2 * (m / nMintsL), iVarM + m );
    return p;
}

/**Function*************************************************************

  Synopsis    [Returns config string for the given truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManSatCheckXY( sat_solver * p, int nLutSize, word * pTruth, int nVars, unsigned uSet, word * pTBound, word * pTFree, Vec_Int_t * vLits )
{
    int iBSet, nBSet = 0;
    int iSSet, nSSet = 0;
    int iFSet, nFSet = 0;
    int nMintsL = (1 << nLutSize);
    int nMintsF = (1 << (2 * nLutSize - 1));
    int v, Value, m, mNew, nMintsFNew, nMintsLNew;
    // collect variable sets
    Dau_DecSortSet( uSet, nVars, &nBSet, &nSSet, &nFSet );
    assert( nBSet + nSSet + nFSet == nVars );
    // check variable bounds
    assert( nSSet + nBSet <= nLutSize );
    assert( nLutSize + nSSet + nFSet <= 2*nLutSize - 1 );
    nMintsFNew = (1 << (nLutSize + nSSet + nFSet));
    // remap minterms
    Vec_IntFill( vLits, nMintsF, -1 );
    for ( m = 0; m < (1 << nVars); m++ )
    {
        mNew = iBSet = iSSet = iFSet = 0;
        for ( v = 0; v < nVars; v++ )
        {
            Value = ((uSet >> (v << 1)) & 3);
            if ( Value == 0 ) // FS
            {
                if ( ((m >> v) & 1) )
                    mNew |= 1 << (nLutSize + nSSet + iFSet);
                iFSet++;
            }
            else if ( Value == 1 ) // BS
            {
                if ( ((m >> v) & 1) )
                    mNew |= 1 << (nSSet + iBSet);
                iBSet++;
            }
            else if ( Value == 3 ) // SS
            {
                if ( ((m >> v) & 1) )
                {
                    mNew |= 1 << iSSet;
                    mNew |= 1 << (nLutSize + iSSet);
                }
                iSSet++;
            }
            else assert( Value == 0 );
        }
        assert( iBSet == nBSet && iFSet == nFSet );
        assert( Vec_IntEntry(vLits, mNew) == -1 );
        Vec_IntWriteEntry( vLits, mNew, Abc_TtGetBit(pTruth, m) );
    }
    // find assumptions
    v = 0;
    Vec_IntForEachEntry( vLits, Value, m )
    {
//        printf( "%d", (Value >= 0) ? Value : 2 );
        if ( Value >= 0 )
            Vec_IntWriteEntry( vLits, v++, Abc_Var2Lit(2 * nMintsL + m, !Value) );
    }
    Vec_IntShrink( vLits, v );
//    printf( " %d\n", Vec_IntSize(vLits) );
    // run SAT solver
    Value = sat_solver_solve( p, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), 0, 0, 0, 0 );
    if ( Value != l_True )
        return 0;
    // collect config
    assert( nSSet + nBSet <= nLutSize );
    *pTBound = 0;
    nMintsLNew = (1 << (nSSet + nBSet));
    for ( m = 0; m < nMintsLNew; m++ )
        if ( sat_solver_var_value(p, m) )
            Abc_TtSetBit( pTBound, m );
    *pTBound = Abc_Tt6Stretch( *pTBound, nSSet + nBSet );
    // collect configs
    assert( nSSet + nFSet + 1 <= nLutSize );
    *pTFree = 0;
    nMintsLNew = (1 << (nSSet + nFSet + 1));
    for ( m = 0; m < nMintsLNew; m++ )
        if ( sat_solver_var_value(p, nMintsL+m) )
            Abc_TtSetBit( pTFree, m );
    *pTFree = Abc_Tt6Stretch( *pTFree, nSSet + nFSet + 1 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Test procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManSatTest2()
{
    int nVars = 6;
    int nLutSize = 4;
    sat_solver * p = If_ManSatBuildXY( nLutSize );
//    char * pDsd = "(abcdefg)";
//    char * pDsd = "([a!bc]d!e)";
    char * pDsd = "0123456789ABCDEF{abcdef}";
    word * pTruth = Dau_DsdToTruth( pDsd, nVars );
    word uBound, uFree;
    Vec_Int_t * vLits = Vec_IntAlloc( 100 );
//    unsigned uSet = (1 << 0) | (1 << 2) | (1 << 4) | (1 << 6);
//    unsigned uSet = (3 << 0) | (1 << 2) | (1 << 8) | (1 << 4);
    unsigned uSet = (1 << 0) | (3 << 2) | (1 << 4) | (1 << 6);
    int RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    assert( RetValue );
    
//    Abc_TtPrintBinary( pTruth, nVars );
//    Abc_TtPrintBinary( &uBound, nLutSize );
//    Abc_TtPrintBinary( &uFree, nLutSize );

    Dau_DsdPrintFromTruth( pTruth, nVars );
    Dau_DsdPrintFromTruth( &uBound, nLutSize );
    Dau_DsdPrintFromTruth( &uFree, nLutSize );
    sat_solver_delete(p);
    Vec_IntFree( vLits );
}

void If_ManSatTest()
{
    int nVars = 4;
    int nLutSize = 3;
    sat_solver * p = If_ManSatBuildXY( nLutSize );
    word t = 0x183C, * pTruth = &t;
    word uBound, uFree;
    unsigned uSet;
    int RetValue;
    Vec_Int_t * vLits = Vec_IntAlloc( 100 );

    
    uSet = (3 << 0) | (1 << 2) | (1 << 4);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (3 << 2) | (1 << 4);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (1 << 2) | (3 << 4);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );

    
    uSet = (3 << 0) | (1 << 2) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (3 << 2) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (1 << 2) | (3 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );

    
    uSet = (3 << 0) | (1 << 4) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (3 << 4) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 0) | (1 << 4) | (3 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );

    
    uSet = (3 << 2) | (1 << 4) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 2) | (3 << 4) | (1 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );
    uSet = (1 << 2) | (1 << 4) | (3 << 6);
    RetValue = If_ManSatCheckXY( p, nLutSize, pTruth, nVars, uSet, &uBound, &uFree, vLits );
    printf( "%d", RetValue );

    printf( "\n" );

    sat_solver_delete(p);
    Vec_IntFree( vLits );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

