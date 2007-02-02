/**CFile****************************************************************

  FileName    [resSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Interface with the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resSat.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "resInt.h"
#include "hop.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Res_SatAddConst1( sat_solver * pSat, int iVar, int fCompl );
extern int Res_SatAddEqual( sat_solver * pSat, int iVar0, int iVar1, int fCompl );
extern int Res_SatAddAnd( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1 );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Loads AIG into the SAT solver for checking resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Res_SatProveUnsat( Abc_Ntk_t * pAig, Vec_Ptr_t * vFanins )
{
    void * pCnf = NULL;
    sat_solver * pSat;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i, nNodes, status;

    // make sure fanins contain POs of the AIG
    pObj = Vec_PtrEntry( vFanins, 0 );
    assert( pObj->pNtk == pAig && Abc_ObjIsPo(pObj) );

    // collect reachable nodes
    vNodes = Abc_NtkDfsNodes( pAig, (Abc_Obj_t **)vFanins->pArray, vFanins->nSize );

    // assign unique numbers to each node
    nNodes = 0;
    Abc_AigConst1(pAig)->pCopy = (void *)nNodes++;
    Abc_NtkForEachPi( pAig, pObj, i )
        pObj->pCopy = (void *)nNodes++;
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pCopy = (void *)nNodes++;
    Vec_PtrForEachEntry( vFanins, pObj, i ) // useful POs
        pObj->pCopy = (void *)nNodes++;

    // start the solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );

    // add clause for the constant node
    Res_SatAddConst1( pSat, (int)Abc_AigConst1(pAig)->pCopy, 0 );
    // add clauses for AND gates
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Res_SatAddAnd( pSat, (int)pObj->pCopy, 
            (int)Abc_ObjFanin0(pObj)->pCopy, (int)Abc_ObjFanin1(pObj)->pCopy, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    Vec_PtrFree( vNodes );
    // add clauses for POs
    Vec_PtrForEachEntry( vFanins, pObj, i )
        Res_SatAddEqual( pSat, (int)pObj->pCopy, 
            (int)Abc_ObjFanin0(pObj)->pCopy, Abc_ObjFaninC0(pObj) );
    // add trivial clauses
    pObj = Vec_PtrEntry(vFanins, 0);
    Res_SatAddConst1( pSat, (int)pObj->pCopy, 0 ); // care-set
    pObj = Vec_PtrEntry(vFanins, 1);
    Res_SatAddConst1( pSat, (int)pObj->pCopy, 0 ); // on-set

    // bookmark the clauses of A
    sat_solver_store_mark_clauses_a( pSat );

    // duplicate the clauses
    pObj = Vec_PtrEntry(vFanins, 1);
    Sat_SolverDoubleClauses( pSat, (int)pObj->pCopy );
    // add the equality constraints
    Vec_PtrForEachEntryStart( vFanins, pObj, i, 2 )
        Res_SatAddEqual( pSat, (int)pObj->pCopy, ((int)pObj->pCopy) + nNodes, 0 );

    // bookmark the roots
    sat_solver_store_mark_roots( pSat );

    // solve the problem
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)10000, (sint64)0, (sint64)0, (sint64)0 );
    if ( status == l_False )
    {
        pCnf = sat_solver_store_release( pSat );
//        printf( "unsat\n" );
    }
    else if ( status == l_True )
    {
//        printf( "sat\n" );
    }
    else
    {
//        printf( "undef\n" );
    }
    sat_solver_delete( pSat );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    [Loads AIG into the SAT solver for constrained simulation.]

  Description [The array of fanins contains exactly two entries: the 
  care set and the functions.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Res_SatSimulateConstr( Abc_Ntk_t * pAig, Vec_Ptr_t * vFanins )
{
    sat_solver * pSat;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i, nNodes;

    // make sure fanins contain POs of the AIG
    pObj = Vec_PtrEntry( vFanins, 0 );
    assert( pObj->pNtk == pAig && Abc_ObjIsPo(pObj) );
    assert( Vec_PtrSize(vFanins) == 2 );

    // collect reachable nodes
    vNodes = Abc_NtkDfsNodes( pAig, (Abc_Obj_t **)vFanins->pArray, vFanins->nSize );

    // assign unique numbers to each node
    nNodes = 0;
    Abc_AigConst1(pAig)->pCopy = (void *)nNodes++;
    Abc_NtkForEachPi( pAig, pObj, i )
        pObj->pCopy = (void *)nNodes++;
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pCopy = (void *)nNodes++;
    Vec_PtrForEachEntry( vFanins, pObj, i ) // useful POs
        pObj->pCopy = (void *)nNodes++;

    // start the solver
    pSat = sat_solver_new();

    // add clause for the constant node
    Res_SatAddConst1( pSat, (int)Abc_AigConst1(pAig)->pCopy, 0 );
    // add clauses for AND gates
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Res_SatAddAnd( pSat, (int)pObj->pCopy, 
            (int)Abc_ObjFanin0(pObj)->pCopy, (int)Abc_ObjFanin1(pObj)->pCopy, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    Vec_PtrFree( vNodes );
    // add clauses for POs
    Vec_PtrForEachEntry( vFanins, pObj, i )
        Res_SatAddEqual( pSat, (int)pObj->pCopy, 
            (int)Abc_ObjFanin0(pObj)->pCopy, Abc_ObjFaninC0(pObj) );

    // add trivial clauses
    pObj = Vec_PtrEntry(vFanins, 0);
    Res_SatAddConst1( pSat, (int)pObj->pCopy, 0 ); // care-set
    pObj = Vec_PtrEntry(vFanins, 1);
    Res_SatAddConst1( pSat, (int)pObj->pCopy, 0 ); // on-set
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Asserts equality of the variable to a constant.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_SatAddConst1( sat_solver * pSat, int iVar, int fCompl )
{
    lit Lit = toLitCond( iVar, fCompl );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit + 1 ) )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Asserts equality of two variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_SatAddEqual( sat_solver * pSat, int iVar0, int iVar1, int fCompl )
{
    lit Lits[2];

    Lits[0] = toLitCond( iVar0, 0 );
    Lits[1] = toLitCond( iVar1, !fCompl );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar0, 1 );
    Lits[1] = toLitCond( iVar1, fCompl );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds constraints for the two-input AND-gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_SatAddAnd( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1 )
{
    lit Lits[3];

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar, 0 );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


