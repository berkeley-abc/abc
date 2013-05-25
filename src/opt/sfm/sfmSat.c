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

  Synopsis    [Creates order of objects in the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkOrderObjects( Sfm_Ntk_t * p )
{
    int i, iNode;
    assert( Vec_IntEntryLast(p->vNodes) == Vec_IntEntry(p->vDivs, Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes)) );
    Vec_IntClear( p->vOrder );
    Vec_IntForEachEntryReverse( p->vNodes, iNode, i )
        Vec_IntPush( p->vOrder, iNode );
    Vec_IntForEachEntryStart( p->vDivs, iNode, i, Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes) )
        Vec_IntPush( p->vOrder, iNode );
}

/**Function*************************************************************

  Synopsis    [Converts a window into a SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkWindowToSolver( Sfm_Ntk_t * p )
{
    Vec_Int_t * vClause;
    int RetValue, Lit, iNode = -1, iFanin, i, k;
    clock_t clk = clock();
    sat_solver * pSat0 = sat_solver_new();
    sat_solver * pSat1 = sat_solver_new();
    sat_solver_setnvars( pSat0, 1 + Vec_IntSize(p->vDivs) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) + 100 );
    sat_solver_setnvars( pSat1, 1 + Vec_IntSize(p->vDivs) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) + 100 );
    // create SAT variables
    p->nSatVars = 1;
    Vec_IntForEachEntryReverse( p->vNodes, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    Vec_IntForEachEntryReverse( p->vLeaves, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    Vec_IntForEachEntryReverse( p->vDivs, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    // add CNF clauses for the TFI
    Sfm_NtkOrderObjects( p );
    Vec_IntForEachEntry( p->vOrder, iNode, i )
    {
        // collect fanin variables
        Vec_IntClear( p->vFaninMap );
        Sfm_ObjForEachFanin( p, iNode, iFanin, k )
            Vec_IntPush( p->vFaninMap, Sfm_ObjSatVar(p, iFanin) );
        Vec_IntPush( p->vFaninMap, Sfm_ObjSatVar(p, iNode) );
        // generate CNF 
        Sfm_TranslateCnf( p->vClauses, (Vec_Str_t *)Vec_WecEntry(p->vCnfs, iNode), p->vFaninMap );
        // add clauses
        Vec_WecForEachLevel( p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( pSat0, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            assert( RetValue );
            RetValue = sat_solver_addclause( pSat1, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            assert( RetValue );
        }
    }
    // get the last node
    iNode = Vec_IntEntryLast( p->vNodes );
    // add unit clause
    Lit = Abc_Var2Lit( Sfm_ObjSatVar(p, iNode), 1 );
    RetValue = sat_solver_addclause( pSat0, &Lit, &Lit + 1 );
    assert( RetValue );
    // add unit clause
    Lit = Abc_Var2Lit( Sfm_ObjSatVar(p, iNode), 0 );
    RetValue = sat_solver_addclause( pSat1, &Lit, &Lit + 1 );
    assert( RetValue );
    // finalize
    sat_solver_compress( pSat0 );
    sat_solver_compress( pSat1 );
    // return the result
    assert( p->pSat0 == NULL );
    assert( p->pSat1 == NULL );
    p->pSat0 = pSat0;
    p->pSat1 = pSat1;
    p->timeCnf += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Takes SAT solver and returns interpolant.]

  Description [If interpolant does not exist, records difference variables.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sfm_ComputeInterpolant( Sfm_Ntk_t * p )
{
    word * pSign, uCube, uTruth = 0;
    int status, i, Div, iVar, nFinal, * pFinal;
    int nVars = sat_solver_nvars( p->pSat1 );
    int iNewLit = Abc_Var2Lit( nVars, 0 );
    sat_solver_setnvars( p->pSat1, nVars + 1 );
    while ( 1 ) 
    {
        // find onset minterm
        status = sat_solver_solve( p->pSat1, &iNewLit, &iNewLit + 1, p->pPars->nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SFM_SAT_UNDEC;
        if ( status == l_False )
            return uTruth;
        assert( status == l_True );
        // collect divisor literals
        Vec_IntClear( p->vLits );
        Vec_IntForEachEntry( p->vDivIds, Div, i )
            Vec_IntPush( p->vLits, sat_solver_var_literal(p->pSat1, Div) );
        // check against offset
        status = sat_solver_solve( p->pSat0, Vec_IntArray(p->vLits), Vec_IntArray(p->vLits) + Vec_IntSize(p->vLits), p->pPars->nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SFM_SAT_UNDEC;
        if ( status == l_True )
            break;
        assert( status == l_False );
        // compute cube and add clause
        nFinal = sat_solver_final( p->pSat0, &pFinal );
        uCube = ~(word)0;
        Vec_IntClear( p->vLits );
        Vec_IntPush( p->vLits, Abc_LitNot(iNewLit) );
        for ( i = 0; i < nFinal; i++ )
        {
            Vec_IntPush( p->vLits, pFinal[i] );
            iVar = Vec_IntFind( p->vDivIds, Abc_Lit2Var(pFinal[i]) );   assert( iVar >= 0 );
            uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
        }
        uTruth |= uCube;
        status = sat_solver_addclause( p->pSat1, Vec_IntArray(p->vLits), Vec_IntArray(p->vLits) + Vec_IntSize(p->vLits) );
        assert( status );
    }
    assert( status == l_True );
    // store the counter-example
    Vec_IntForEachEntry( p->vDivVars, iVar, i )
        if ( sat_solver_var_value(p->pSat1, iVar) ^ sat_solver_var_value(p->pSat0, iVar) ) // insert 1
        {
            pSign = Vec_WrdEntryP( p->vDivCexes, i );
            assert( !Abc_InfoHasBit( (unsigned *)pSign, p->nCexes) );
            Abc_InfoXorBit( (unsigned *)pSign, p->nCexes );
        }
    p->nCexes++;
    return SFM_SAT_SAT;
}

/**Function*************************************************************

  Synopsis    [Checks resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
void Sfm_ComputeInterpolantCheck( Sfm_Ntk_t * p )
{
    int iNode = 3;
    int iDiv0 = 6;
    int iDiv1 = 7;
    word uTruth;
//    int i;
//    Sfm_NtkForEachNode( p, i )
    {
        Sfm_NtkCreateWindow( p, iNode, 1 );
        Sfm_NtkWindowToSolver( p );

        // collect SAT variables of divisors
        Vec_IntClear( p->vDivIds );
        Vec_IntPush( p->vDivIds, Sfm_ObjSatVar(p, iDiv0) );
        Vec_IntPush( p->vDivIds, Sfm_ObjSatVar(p, iDiv1) );

        uTruth = Sfm_ComputeInterpolant( p->pSat1, p->pSat0, p->vDivIds, p->vLits, p->vDiffs, 0 );

        if ( uTruth == SFM_SAT_SAT )
            printf( "The problem is SAT.\n" );
        else if ( uTruth == SFM_SAT_UNDEC )
            printf( "The problem is UNDEC.\n" );
        else
            Kit_DsdPrintFromTruth( (unsigned *)&uTruth, 2 ); printf( "\n" );

        Sfm_NtkCleanVars( p, p->nSatVars );
        sat_solver_delete( p->pSat0 );  p->pSat0 = NULL;
        sat_solver_delete( p->pSat1 );  p->pSat1 = NULL;
    }
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

