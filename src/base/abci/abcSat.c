/**CFile****************************************************************

  FileName    [abcSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to solve the miter using the internal SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  Abc_NodeAddClauses( solver * pSat, char * pSop0, char * pSop1, Abc_Obj_t * pNode, Vec_Int_t * vVars );
static int  Abc_NodeAddClausesTop( solver * pSat, Abc_Obj_t * pNode, Vec_Int_t * vVars );

static solver * Abc_NtkMiterSatCreate2( Abc_Ntk_t * pNtk );

static Vec_Int_t * Abc_NtkGetCiSatVarNums( Abc_Ntk_t * pNtk );

static nMuxes;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using an internal SAT solver.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterSat_OldAndRusty( Abc_Ntk_t * pNtk, int nSeconds, int fVerbose )
{
    solver * pSat;
    lbool   status;
    int RetValue, clk;

    assert( Abc_NtkIsBddLogic(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    if ( Abc_NtkPoNum(pNtk) > 1 )
        fprintf( stdout, "Warning: The miter has %d outputs. SAT will try to prove all of them.\n", Abc_NtkPoNum(pNtk) );

    // load clauses into the solver
    clk = clock();
    pSat = Abc_NtkMiterSatCreate( pNtk );
    if ( pSat == NULL )
        return 1;
//    printf( "Created SAT problem with %d variable and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );

    // simplify the problem
    clk = clock();
    status = solver_simplify(pSat);
//    printf( "Simplified the problem to %d variables and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );
    if ( status == 0 )
    {
        solver_delete( pSat );
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return 1;
    }

    // solve the miter
    clk = clock();
    if ( fVerbose )
        pSat->verbosity = 1;
    status = solver_solve( pSat, NULL, NULL, nSeconds );
    if ( status == l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if ( status == l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if ( status == l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }
    else
        assert( 0 );
//    PRT( "SAT solver time", clock() - clk );

    // if the problem is SAT, get the counterexample
    if ( status == l_True )
    {
        Vec_Int_t * vCiIds = Abc_NtkGetCiIds( pNtk );
        pNtk->pModel = solver_get_model( pSat, vCiIds->pArray, vCiIds->nSize );
        Vec_IntFree( vCiIds );
    }
    // free the solver
    solver_delete( pSat );
    return RetValue;
}
 
/**Function*************************************************************

  Synopsis    [Sets up the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
solver * Abc_NtkMiterSatCreate( Abc_Ntk_t * pNtk )
{
    solver * pSat;
    Extra_MmFlex_t * pMmFlex;
    Abc_Obj_t * pNode;
    Vec_Str_t * vCube;
    Vec_Int_t * vVars;
    char * pSop0, * pSop1;
    int i, clk = clock();

    assert( Abc_NtkIsBddLogic(pNtk) );

    // start the data structures
    pSat    = solver_new();
    pMmFlex = Extra_MmFlexStart();
    vCube   = Vec_StrAlloc( 100 );
    vVars   = Vec_IntAlloc( 100 );

    // add clauses for each internal nodes
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        // derive SOPs for both phases of the node
        Abc_NodeBddToCnf( pNode, pMmFlex, vCube, &pSop0, &pSop1 );
        // add the clauses to the solver
        if ( !Abc_NodeAddClauses( pSat, pSop0, pSop1, pNode, vVars ) )
        {
            solver_delete( pSat );
            return NULL;
        }
    }
    // add clauses for the POs
    if ( !Abc_NodeAddClausesTop( pSat, Abc_NtkPo(pNtk, Abc_NtkPoNum(pNtk)-1), vVars ) )
    {
        solver_delete( pSat );
        return NULL;
    }
//    Asat_SolverWriteDimacs( pSat, "test.cnf", NULL, NULL, 0 );

    PRT( "Creating solver", clock() - clk );

    // delete
    Vec_StrFree( vCube );
    Vec_IntFree( vVars );
    Extra_MmFlexStop( pMmFlex, 0 );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Adds clauses for the internal node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeAddClauses( solver * pSat, char * pSop0, char * pSop1, Abc_Obj_t * pNode, Vec_Int_t * vVars )
{
    Abc_Obj_t * pFanin;
    int i, c, nFanins;
    char * pCube;

    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum( pSop0 ) );

    if ( nFanins == 0 )
    {
        vVars->nSize = 0;
        if ( Abc_SopIsConst1(pSop1) )
            Vec_IntPush( vVars, toLit(pNode->Id) );
        else
            Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
    }
 
    // add clauses for the negative phase
    for ( c = 0; ; c++ )
    {
        // get the cube
        pCube = pSop0 + c * (nFanins + 3);
        if ( *pCube == 0 )
            break;
        // add the clause
        vVars->nSize = 0;
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( pCube[i] == '0' )
                Vec_IntPush( vVars, toLit(pFanin->Id) );
            else if ( pCube[i] == '1' )
                Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        }
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }

    // add clauses for the positive phase
    for ( c = 0; ; c++ )
    {
        // get the cube
        pCube = pSop1 + c * (nFanins + 3);
        if ( *pCube == 0 )
            break;
        // add the clause
        vVars->nSize = 0;
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( pCube[i] == '0' )
                Vec_IntPush( vVars, toLit(pFanin->Id) );
            else if ( pCube[i] == '1' )
                Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        }
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds clauses for the PO node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeAddClausesTop( solver * pSat, Abc_Obj_t * pNode, Vec_Int_t * vVars )
{
    Abc_Obj_t * pFanin;

    pFanin = Abc_ObjFanin0(pNode);
    if ( Abc_ObjFaninC0(pNode) )
    {
        vVars->nSize = 0;
        Vec_IntPush( vVars, toLit(pFanin->Id) );
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;

        vVars->nSize = 0;
        Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }
    else
    {
        vVars->nSize = 0;
        Vec_IntPush( vVars, neg(toLit(pFanin->Id)) );
        Vec_IntPush( vVars, toLit(pNode->Id) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;

        vVars->nSize = 0;
        Vec_IntPush( vVars, toLit(pFanin->Id) );
        Vec_IntPush( vVars, neg(toLit(pNode->Id)) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }

    vVars->nSize = 0;
    Vec_IntPush( vVars, toLit(pNode->Id) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}











/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using an internal SAT solver.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterSat( Abc_Ntk_t * pNtk, int nSeconds, int fVerbose )
{
    solver * pSat;
    lbool   status;
    int RetValue, clk;

    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    if ( Abc_NtkPoNum(pNtk) > 1 )
        fprintf( stdout, "Warning: The miter has %d outputs. SAT will try to prove all of them.\n", Abc_NtkPoNum(pNtk) );

    // load clauses into the solver
    clk = clock();
    pSat = Abc_NtkMiterSatCreate2( pNtk );
    if ( pSat == NULL )
        return 1;
//    printf( "Created SAT problem with %d variable and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );

    // simplify the problem
    clk = clock();
    status = solver_simplify(pSat);
//    printf( "Simplified the problem to %d variables and %d clauses. ", solver_nvars(pSat), solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );
    if ( status == 0 )
    {
        solver_delete( pSat );
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return 1;
    }

    // solve the miter
    clk = clock();
    if ( fVerbose )
        pSat->verbosity = 1;
    status = solver_solve( pSat, NULL, NULL, nSeconds );
    if ( status == l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if ( status == l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if ( status == l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }
    else
        assert( 0 );
    PRT( "SAT solver time", clock() - clk );

    // if the problem is SAT, get the counterexample
    if ( status == l_True )
    {
//        Vec_Int_t * vCiIds = Abc_NtkGetCiIds( pNtk );
        Vec_Int_t * vCiIds = Abc_NtkGetCiSatVarNums( pNtk );
        pNtk->pModel = solver_get_model( pSat, vCiIds->pArray, vCiIds->nSize );
        Vec_IntFree( vCiIds );
    }
    // free the solver
    solver_delete( pSat );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns the array of CI IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkGetCiSatVarNums( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vCiIds;
    Abc_Obj_t * pObj;
    int i;
    vCiIds = Vec_IntAlloc( Abc_NtkCiNum(pNtk) );
    Abc_NtkForEachCi( pNtk, pObj, i )
        Vec_IntPush( vCiIds, (int)pObj->pCopy );
    return vCiIds;
}



 
/**Function*************************************************************

  Synopsis    [Adds trivial clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkClauseTriv( solver * pSat, Abc_Obj_t * pNode, Vec_Int_t * vVars )
{
//printf( "Adding triv %d.         %d\n", Abc_ObjRegular(pNode)->Id, (int)pSat->solver_stats.clauses );
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond( (int)Abc_ObjRegular(pNode)->pCopy, Abc_ObjIsComplement(pNode) ) );
//    Vec_IntPush( vVars, toLitCond( (int)Abc_ObjRegular(pNode)->Id, Abc_ObjIsComplement(pNode) ) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}
 
/**Function*************************************************************

  Synopsis    [Adds trivial clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkClauseAnd( solver * pSat, Abc_Obj_t * pNode, Vec_Ptr_t * vSuper, Vec_Int_t * vVars )
{
    int fComp1, Var, Var1, i;
//printf( "Adding AND %d.  (%d)    %d\n", pNode->Id, vSuper->nSize+1, (int)pSat->solver_stats.clauses );

    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );

//    nVars = solver_nvars(pSat);
    Var = (int)pNode->pCopy;
//    Var = pNode->Id;

//    assert( Var  < nVars ); 
    for ( i = 0; i < vSuper->nSize; i++ )
    {
        // get the predecessor nodes
        // get the complemented attributes of the nodes
        fComp1 = Abc_ObjIsComplement(vSuper->pArray[i]);
        // determine the variable numbers
        Var1 = (int)Abc_ObjRegular(vSuper->pArray[i])->pCopy;
//        Var1 = (int)Abc_ObjRegular(vSuper->pArray[i])->Id;

        // check that the variables are in the SAT manager
//        assert( Var1 < nVars );

        // suppose the AND-gate is A * B = C
        // add !A => !C   or   A + !C
    //  fprintf( pFile, "%d %d 0%c", Var1, -Var, 10 );
        vVars->nSize = 0;
        Vec_IntPush( vVars, toLitCond(Var1, fComp1) );
        Vec_IntPush( vVars, toLitCond(Var,  1     ) );
        if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
            return 0;
    }

    // add A & B => C   or   !A + !B + C
//  fprintf( pFile, "%d %d %d 0%c", -Var1, -Var2, Var, 10 );
    vVars->nSize = 0;
    for ( i = 0; i < vSuper->nSize; i++ )
    {
        // get the predecessor nodes
        // get the complemented attributes of the nodes
        fComp1 = Abc_ObjIsComplement(vSuper->pArray[i]);
        // determine the variable numbers
        Var1 = (int)Abc_ObjRegular(vSuper->pArray[i])->pCopy;
//        Var1 = (int)Abc_ObjRegular(vSuper->pArray[i])->Id;
        // add this variable to the array
        Vec_IntPush( vVars, toLitCond(Var1, !fComp1) );
    }
    Vec_IntPush( vVars, toLitCond(Var, 0) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}
 
/**Function*************************************************************

  Synopsis    [Adds trivial clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkClauseMux( solver * pSat, Abc_Obj_t * pNode, Abc_Obj_t * pNodeC, Abc_Obj_t * pNodeT, Abc_Obj_t * pNodeE, Vec_Int_t * vVars )
{
    int VarF, VarI, VarT, VarE, fCompT, fCompE;
//printf( "Adding mux %d.         %d\n", pNode->Id, (int)pSat->solver_stats.clauses );

    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_NodeIsMuxType( pNode ) );
    // get the variable numbers
    VarF = (int)pNode->pCopy;
    VarI = (int)pNodeC->pCopy;
    VarT = (int)Abc_ObjRegular(pNodeT)->pCopy;
    VarE = (int)Abc_ObjRegular(pNodeE)->pCopy;
//    VarF = (int)pNode->Id;
//    VarI = (int)pNodeC->Id;
//    VarT = (int)Abc_ObjRegular(pNodeT)->Id;
//    VarE = (int)Abc_ObjRegular(pNodeE)->Id;

    // get the complementation flags
    fCompT = Abc_ObjIsComplement(pNodeT);
    fCompE = Abc_ObjIsComplement(pNodeE);

    // f = ITE(i, t, e)
    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'
    // create four clauses
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarI,  1) );
    Vec_IntPush( vVars, toLitCond(VarT,  1^fCompT) );
    Vec_IntPush( vVars, toLitCond(VarF,  0) );
    if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
        return 0;
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarI,  1) );
    Vec_IntPush( vVars, toLitCond(VarT,  0^fCompT) );
    Vec_IntPush( vVars, toLitCond(VarF,  1) );
    if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
        return 0;
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarI,  0) );
    Vec_IntPush( vVars, toLitCond(VarE,  1^fCompE) );
    Vec_IntPush( vVars, toLitCond(VarF,  0) );
    if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
        return 0;
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarI,  0) );
    Vec_IntPush( vVars, toLitCond(VarE,  0^fCompE) );
    Vec_IntPush( vVars, toLitCond(VarF,  1) );
    if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
        return 0;
 
    if ( VarT == VarE )
    {
//        assert( fCompT == !fCompE );
        return 1;
    }

    // two additional clauses
    // t' & e' -> f'       t  + e   + f'
    // t  & e  -> f        t' + e'  + f 
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarT,  0^fCompT) );
    Vec_IntPush( vVars, toLitCond(VarE,  0^fCompE) );
    Vec_IntPush( vVars, toLitCond(VarF,  1) );
    if ( !solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize ) )
        return 0;
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond(VarT,  1^fCompT) );
    Vec_IntPush( vVars, toLitCond(VarE,  1^fCompE) );
    Vec_IntPush( vVars, toLitCond(VarF,  0) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}

/**Function*************************************************************

  Synopsis    [Returns the array of nodes to be combined into one multi-input AND-gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCollectSupergate_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vSuper, int fFirst, int fStopAtMux )
{
    int RetValue1, RetValue2, i;
    // check if the node is visited
    if ( Abc_ObjRegular(pNode)->fMarkB )
    {
        // check if the node occurs in the same polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == pNode )
                return 1;
        // check if the node is present in the opposite polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == Abc_ObjNot(pNode) )
                return -1;
        assert( 0 );
        return 0;
    }
    // if the new node is complemented or a PI, another gate begins
    if ( !fFirst )
    if ( Abc_ObjIsComplement(pNode) || !Abc_ObjIsNode(pNode) || Abc_ObjFanoutNum(pNode) > 1 || fStopAtMux && Abc_NodeIsMuxType(pNode) )
    {
        Vec_PtrPush( vSuper, pNode );
        Abc_ObjRegular(pNode)->fMarkB = 1;
        return 0;
    }
    assert( !Abc_ObjIsComplement(pNode) );
    assert( Abc_ObjIsNode(pNode) );
    // go through the branches
    RetValue1 = Abc_NtkCollectSupergate_rec( Abc_ObjChild0(pNode), vSuper, 0, fStopAtMux );
    RetValue2 = Abc_NtkCollectSupergate_rec( Abc_ObjChild1(pNode), vSuper, 0, fStopAtMux );
    if ( RetValue1 == -1 || RetValue2 == -1 )
        return -1;
    // return 1 if at least one branch has a duplicate
    return RetValue1 || RetValue2;
}

/**Function*************************************************************

  Synopsis    [Returns the array of nodes to be combined into one multi-input AND-gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCollectSupergate( Abc_Obj_t * pNode, int fStopAtMux, Vec_Ptr_t * vNodes )
{
    int RetValue, i;
    assert( !Abc_ObjIsComplement(pNode) );
    // collect the nodes in the implication supergate
    Vec_PtrClear( vNodes );
    RetValue = Abc_NtkCollectSupergate_rec( pNode, vNodes, 1, fStopAtMux );
    assert( vNodes->nSize > 1 );
    // unmark the visited nodes
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjRegular((Abc_Obj_t *)vNodes->pArray[i])->fMarkB = 0;
    // if we found the node and its complement in the same implication supergate, 
    // return empty set of nodes (meaning that we should use constant-0 node)
    if ( RetValue == -1 )
        vNodes->nSize = 0;
}


/**Function*************************************************************

  Synopsis    [Sets up the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterSatCreate2Int( solver * pSat, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pFanin, * pNodeC, * pNodeT, * pNodeE;
    Vec_Ptr_t * vNodes, * vSuper;
    Vec_Int_t * vVars;
    int i, k, fUseMuxes = 1;

    assert( Abc_NtkIsStrash(pNtk) );

    // start the data structures
    vNodes = Vec_PtrAlloc( 1000 );   // the nodes corresponding to vars in the solver
    vSuper = Vec_PtrAlloc( 100 );    // the nodes belonging to the given implication supergate
    vVars  = Vec_IntAlloc( 100 );    // the temporary array for variables in the clause

    // add the clause for the constant node
    pNode = Abc_NtkConst1(pNtk);
    pNode->fMarkA = 1;
    pNode->pCopy = (Abc_Obj_t *)vNodes->nSize;
    Vec_PtrPush( vNodes, pNode );
    Abc_NtkClauseTriv( pSat, pNode, vVars );

    // collect the nodes that need clauses and top-level assignments
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        // get the fanin
        pFanin = Abc_ObjFanin0(pNode);
        // create the node's variable
        if ( pFanin->fMarkA == 0 )
        {
            pFanin->fMarkA = 1;
            pFanin->pCopy = (Abc_Obj_t *)vNodes->nSize;
            Vec_PtrPush( vNodes, pFanin );
        }
        // add the trivial clause
        if ( !Abc_NtkClauseTriv( pSat, Abc_ObjChild0(pNode), vVars ) )
            return 0;
    }

    // add the clauses
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        assert( !Abc_ObjIsComplement(pNode) );
        if ( !Abc_NodeIsAigAnd(pNode) )
            continue;
//printf( "%d ", pNode->Id );

        // add the clauses
        if ( fUseMuxes && Abc_NodeIsMuxType(pNode) )
        {
            nMuxes++;

            pNodeC = Abc_NodeRecognizeMux( pNode, &pNodeT, &pNodeE );
            Vec_PtrClear( vSuper );
            Vec_PtrPush( vSuper, pNodeC );
            Vec_PtrPush( vSuper, pNodeT );
            Vec_PtrPush( vSuper, pNodeE );
            // add the fanin nodes to explore
            Vec_PtrForEachEntry( vSuper, pFanin, k )
            {
                pFanin = Abc_ObjRegular(pFanin);
                if ( pFanin->fMarkA == 0 )
                {
                    pFanin->fMarkA = 1;
                    pFanin->pCopy = (Abc_Obj_t *)vNodes->nSize;
                    Vec_PtrPush( vNodes, pFanin );
                }
            }
            // add the clauses
            if ( !Abc_NtkClauseMux( pSat, pNode, pNodeC, pNodeT, pNodeE, vVars ) )
                return 0;
        }
        else
        {
            // get the supergate
            Abc_NtkCollectSupergate( pNode, fUseMuxes, vSuper );
            // add the fanin nodes to explore
            Vec_PtrForEachEntry( vSuper, pFanin, k )
            {
                pFanin = Abc_ObjRegular(pFanin);
                if ( pFanin->fMarkA == 0 )
                {
                    pFanin->fMarkA = 1;
                    pFanin->pCopy = (Abc_Obj_t *)vNodes->nSize;
                    Vec_PtrPush( vNodes, pFanin );
                }
            }
            // add the clauses
            if ( vSuper->nSize == 0 )
            {
                if ( !Abc_NtkClauseTriv( pSat, Abc_ObjNot(pNode), vVars ) )
                    return 0;
            }
            else
            {
                if ( !Abc_NtkClauseAnd( pSat, pNode, vSuper, vVars ) )
                    return 0;
            }
        }
    }

    // delete
    Vec_IntFree( vVars );
    Vec_PtrFree( vNodes );
    Vec_PtrFree( vSuper );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Sets up the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
solver * Abc_NtkMiterSatCreate2( Abc_Ntk_t * pNtk )
{
    solver * pSat;
    Abc_Obj_t * pNode;
    int RetValue, i, clk = clock();

    nMuxes = 0;

    pSat = solver_new();
    RetValue = Abc_NtkMiterSatCreate2Int( pSat, pNtk );
    Abc_NtkForEachObj( pNtk, pNode, i )
        pNode->fMarkA = 0;
//    Asat_SolverWriteDimacs( pSat, "temp_sat.cnf", NULL, NULL, 1 );
    if ( RetValue == 0 )
    {
        solver_delete(pSat);
        return NULL;
    }
    printf( "The number of MUXes detected = %d (%5.2f %% of logic).  ", nMuxes, 300.0*nMuxes/Abc_NtkNodeNum(pNtk) );
    PRT( "Creating solver", clock() - clk );
    return pSat;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


