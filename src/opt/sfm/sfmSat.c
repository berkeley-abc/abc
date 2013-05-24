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

  Synopsis    [Converts a window into a SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkWin2Sat( Sfm_Ntk_t * p )
{
    Vec_Int_t * vClause;
    int RetValue, Lit, iNode = -1, iFanin, i, k, c;
    sat_solver * pSat0 = sat_solver_new();
    sat_solver * pSat1 = sat_solver_new();
    sat_solver_setnvars( pSat0, 1 + Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) );
    sat_solver_setnvars( pSat1, 1 + Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) );
    // create SAT variables
    p->nSatVars = 1;
    Vec_IntForEachEntryReverse( p->vNodes, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    Vec_IntForEachEntryReverse( p->vLeaves, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    Vec_IntForEachEntryReverse( p->vDivs, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    // add CNF clauses
    for ( c = 0; c < 2; c++ )
    {
        Vec_Int_t * vObjs = c ? p->vDivs : p->vNodes;
        Vec_IntForEachEntryReverse( vObjs, iNode, i )
        {
            // collect fanin variables
            Vec_IntClear( p->vFaninMap );
            Sfm_NodeForEachFanin( p, iNode, iFanin, k )
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
}

/**Function*************************************************************

  Synopsis    [Takes SAT solver and returns interpolant.]

  Description [If interpolant does not exist, returns diff SAT variables.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sfm_ComputeInterpolant( sat_solver * pSatOn, sat_solver * pSatOff, Vec_Int_t * vDivIds, Vec_Int_t * vLits, Vec_Int_t * vDiffs, int nBTLimit )
{
    word uTruth = 0, uCube;
    int status, i, Div, iVar, nFinal, * pFinal;
    int nVars = sat_solver_nvars(pSatOn);
    int iNewLit = Abc_Var2Lit( nVars, 0 );
    int RetValue;
    sat_solver_setnvars( pSatOn, nVars + 1 );
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
        Vec_IntForEachEntry( vDivIds, Div, i )
//            Vec_IntPush( vLits, Abc_LitNot(sat_solver_var_literal(pSatOn, Div)) );
            Vec_IntPush( vLits, sat_solver_var_literal(pSatOn, Div) );
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
            iVar = Vec_IntFind( vDivIds, Abc_Lit2Var(pFinal[i]) );   assert( iVar >= 0 );
            uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
        }
        uTruth |= uCube;
        RetValue = sat_solver_addclause( pSatOn, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );
        assert( RetValue );
    }
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_ComputeInterpolantCheck( Sfm_Ntk_t * p )
{
    int iNode = 3;
    int iDiv0 = 6;
    int iDiv1 = 7;
    word uTruth;
//    int i;
//    Sfm_NtkForEachNode( p, i )
    {
        Sfm_NtkWindow( p, iNode, 1 );
        Sfm_NtkWin2Sat( p );

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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

