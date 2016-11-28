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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Constructs SAT solver for the window.]

  Description [The window for the pivot node (Pivot) is represented as
  a DFS ordered array of objects (vWinObjs) whose indexed in the array
  (which will be used as SAT variables) are given in array vObj2Var.
  The TFO nodes are listed as the last ones in vWinObjs. The root nodes
  are labeled with Abc_LitIsCompl() in vTfo and also given in vRoots.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Sbd_ManSatSolver( sat_solver * pSat, Gia_Man_t * p, int Pivot, Vec_Int_t * vWinObjs, Vec_Int_t * vObj2Var, Vec_Int_t * vTfo, Vec_Int_t * vRoots )
{
    Gia_Obj_t * pObj;
    int i, iObj, Fan0, Fan1, Node, fCompl0, fCompl1, RetValue;
    int PivotVar = Vec_IntEntry(vObj2Var, Pivot);
    // create SAT solver
    if ( pSat == NULL )
        pSat = sat_solver_new();
    else
        sat_solver_restart( pSat );
    sat_solver_setnvars( pSat, Vec_IntSize(vWinObjs) + Vec_IntSize(vTfo) + Vec_IntSize(vRoots) + 32 );
    // add clauses for all nodes
    Vec_IntForEachEntry( vWinObjs, iObj, i )
    {
        pObj = Gia_ManObj( p, iObj );
        if ( Gia_ObjIsCi(pObj) )
            continue;
        assert( Gia_ObjIsAnd(pObj) );
        Node = Vec_IntEntry( vObj2Var, iObj );
        Fan0 = Vec_IntEntry( vObj2Var, Gia_ObjFaninId0(pObj, iObj) );
        Fan1 = Vec_IntEntry( vObj2Var, Gia_ObjFaninId1(pObj, iObj) );
        fCompl0 = Gia_ObjFaninC0(pObj);
        fCompl1 = Gia_ObjFaninC1(pObj);
        if ( Gia_ObjIsXor(pObj) )
            sat_solver_add_xor( pSat, Node, Fan0, Fan1, fCompl0 ^ fCompl1 );
        else
            sat_solver_add_and( pSat, Node, Fan0, Fan1, fCompl0, fCompl1, 0 );
    }
    // add second clauses for the TFO
    Vec_IntForEachEntryStart( vWinObjs, iObj, i, Vec_IntSize(vWinObjs) - Vec_IntSize(vTfo) )
    {
        pObj = Gia_ManObj( p, iObj );
        assert( Gia_ObjIsAnd(pObj) );
        Node = Vec_IntEntry( vObj2Var, iObj ) + Vec_IntSize(vTfo);
        Fan0 = Vec_IntEntry( vObj2Var, Gia_ObjFaninId0(pObj, iObj) );
        Fan1 = Vec_IntEntry( vObj2Var, Gia_ObjFaninId1(pObj, iObj) );
        Fan0 = Fan0 <= PivotVar ? Fan0 : Fan0 + Vec_IntSize(vTfo);
        Fan1 = Fan1 <= PivotVar ? Fan1 : Fan1 + Vec_IntSize(vTfo);
        fCompl0 = Gia_ObjFaninC0(pObj) ^ (Fan0 == PivotVar);
        fCompl1 = Gia_ObjFaninC1(pObj) ^ (Fan1 == PivotVar);
        if ( Gia_ObjIsXor(pObj) )
            sat_solver_add_xor( pSat, Node, Fan0, Fan1, fCompl0 ^ fCompl1 );
        else
            sat_solver_add_and( pSat, Node, Fan0, Fan1, fCompl0, fCompl1, 0 );
    }
    if ( Vec_IntSize(vRoots) > 0 )
    {
        // create XOR clauses for the roots
        int nVars = Vec_IntSize(vWinObjs) + Vec_IntSize(vTfo);
        Vec_Int_t * vFaninVars = Vec_IntAlloc( Vec_IntSize(vRoots) );
        Vec_IntForEachEntry( vRoots, iObj, i )
        {
            Vec_IntPush( vFaninVars, Abc_Var2Lit(nVars, 0) );
            Node = Vec_IntEntry( vObj2Var, iObj );
            sat_solver_add_xor( pSat, Node, Node + Vec_IntSize(vTfo), nVars++, 0 );
        }
        // make OR clause for the last nRoots variables
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vFaninVars), Vec_IntLimit(vFaninVars) );
        Vec_IntFree( vFaninVars );
        if ( RetValue == 0 )
            return 0;
        assert( sat_solver_nvars(pSat) == nVars + 32 );
    }
    // finalize
    RetValue = sat_solver_simplify( pSat );
    if ( RetValue == 0 )
    {
        sat_solver_delete( pSat );
        return NULL;    
    }
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Solves one SAT problem.]

  Description [Computes node function for PivotVar with fanins in vDivVars
  using don't-care represented in the SAT solver. Uses array vValues to 
  return the values of the first Vec_IntSize(vValues) SAT variables in case
  the implementation of the node with the given fanins does not exist.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sbd_ManSolve( sat_solver * pSat, int PivotVar, int FreeVar, Vec_Int_t * vDivVars, Vec_Int_t * vValues, Vec_Int_t * vTemp )
{
    int nBTLimit = 0;
    word uCube, uTruth = 0;
    int status, i, iVar, nFinal, * pFinal, pLits[2], nIter = 0;
    pLits[0] = Abc_Var2Lit( PivotVar, 0 ); // F = 1
    pLits[1] = Abc_Var2Lit( FreeVar, 0 );  // iNewLit
    assert( Vec_IntSize(vValues) <= sat_solver_nvars(pSat) );
    while ( 1 ) 
    {
        // find onset minterm
        status = sat_solver_solve( pSat, pLits, pLits + 2, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SBD_SAT_UNDEC;
        if ( status == l_False )
            return uTruth;
        assert( status == l_True );
        // remember variable values
        for ( i = 0; i < Vec_IntSize(vValues); i++ )
            Vec_IntWriteEntry( vValues, i, sat_solver_var_value(pSat, i) );
        // collect divisor literals
        Vec_IntClear( vTemp );
        Vec_IntPush( vTemp, Abc_LitNot(pLits[0]) ); // F = 0
        Vec_IntForEachEntry( vDivVars, iVar, i )
            Vec_IntPush( vTemp, sat_solver_var_literal(pSat, iVar) );
        // check against offset
        status = sat_solver_solve( pSat, Vec_IntArray(vTemp), Vec_IntArray(vTemp) + Vec_IntSize(vTemp), nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return SBD_SAT_UNDEC;
        if ( status == l_True )
            break;
        assert( status == l_False );
        // compute cube and add clause
        nFinal = sat_solver_final( pSat, &pFinal );
        uCube = ~(word)0;
        Vec_IntClear( vTemp );
        Vec_IntPush( vTemp, Abc_LitNot(pLits[1]) ); // NOT(iNewLit)
        for ( i = 0; i < nFinal; i++ )
        {
            if ( pFinal[i] == pLits[0] )
                continue;
            Vec_IntPush( vTemp, pFinal[i] );
            iVar = Vec_IntFind( vDivVars, Abc_Lit2Var(pFinal[i]) );   assert( iVar >= 0 );
            uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
        }
        uTruth |= uCube;
        status = sat_solver_addclause( pSat, Vec_IntArray(vTemp), Vec_IntArray(vTemp) + Vec_IntSize(vTemp) );
        assert( status );
        nIter++;
    }
    assert( status == l_True );
    // store the counter-example
    for ( i = 0; i < Vec_IntSize(vValues); i++ )
        Vec_IntAddToEntry( vValues, i, 2*sat_solver_var_value(pSat, i) );
    return SBD_SAT_SAT;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

