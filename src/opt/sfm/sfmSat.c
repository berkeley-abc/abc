/**CFile****************************************************************

  FileName    [sfmSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [SAT-based procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static word s_Truths6[6] = {
    ABC_CONST(0xAAAAAAAAAAAAAAAA),
    ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0),
    ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000),
    ABC_CONST(0xFFFFFFFF00000000)
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Takes SAT solver and returns interpolant.]

  Description [If interpolant does not exist, returns diff SAT variables.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sfm_ComputeInterpolant( sat_solver * pSatOn, sat_solver * pSatOff, Vec_Int_t * vDivs, Vec_Int_t * vLits, Vec_Int_t * vDiffs, int nBTLimit )
{
    word uTruth = 0, uCube;
    int status, i, Div, iVar, nFinal, * pFinal;
    int nVars = sat_solver_nvars(pSatOn);
    int iNewLit = Abc_Var2Lit( nVars, 0 );
    while ( 1 ) 
    {
        // find onset minterm
        status = sat_solver_solve( pSatOn, &iNewLit, &iNewLit + 1, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SFM_SAT_UNDEC;
        if ( status == l_False )
            return uTruth;
        assert( status == l_True );
        // collect literals
        Vec_IntClear( vLits );
        Vec_IntForEachEntry( vDivs, Div, i )
            Vec_IntPush( vLits, Abc_LitNot(sat_solver_var_literal(pSatOn, Div)) );
        // check against offset
        status = sat_solver_solve( pSatOff, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SFM_SAT_UNDEC;
        if ( status == l_True )
        {
            Vec_IntClear( vDiffs );
            for ( i = 0; i < nVars; i++ )
                Vec_IntPush( vDiffs, sat_solver_var_value(pSatOn, i) ^ sat_solver_var_value(pSatOff, i) );
            return SFM_SAT_SAT;
        }
        assert( status == l_False );
        // compute cube and add clause
        nFinal = sat_solver_final( pSatOff, &pFinal );
        uCube = ~(word)0;
        Vec_IntClear( vLits );
        Vec_IntPush( vLits, Abc_LitNot(iNewLit) );
        for ( i = 0; i < nFinal; i++ )
        {
            Vec_IntPush( vLits, pFinal[i] );
            iVar = Vec_IntFind( vDivs, Abc_Lit2Var(pFinal[i]) );   assert( iVar >= 0 );
            uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
        }
        uTruth |= uCube;
        sat_solver_addclause( pSatOn, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );
    }
    assert( 0 );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

