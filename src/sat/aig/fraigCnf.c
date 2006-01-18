/**CFile****************************************************************

  FileName    [fraigCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fraigCnf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Adds trivial clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ClauseTriv( solver * pSat, Aig_Node_t * pNode, Vec_Int_t * vVars )
{
//printf( "Adding triv %d.         %d\n", Aig_Regular(pNode)->Id, (int)pSat->solver_stats.clauses );
    vVars->nSize = 0;
    Vec_IntPush( vVars, toLitCond( Aig_Regular(pNode)->Data, Aig_IsComplement(pNode) ) );
//    Vec_IntPush( vVars, toLitCond( (int)Aig_Regular(pNode)->Id, Aig_IsComplement(pNode) ) );
    return solver_addclause( pSat, vVars->pArray, vVars->pArray + vVars->nSize );
}
 
/**Function*************************************************************

  Synopsis    [Adds trivial clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ClauseAnd( solver * pSat, Aig_Node_t * pNode, Vec_Ptr_t * vSuper, Vec_Int_t * vVars )
{
    int fComp1, Var, Var1, i;
//printf( "Adding AND %d.  (%d)    %d\n", pNode->Id, vSuper->nSize+1, (int)pSat->solver_stats.clauses );

    assert( !Aig_IsComplement( pNode ) );
    assert( Aig_NodeIsAnd( pNode ) );

//    nVars = solver_nvars(pSat);
    Var = pNode->Data;
//    Var = pNode->Id;

//    assert( Var  < nVars ); 
    for ( i = 0; i < vSuper->nSize; i++ )
    {
        // get the predecessor nodes
        // get the complemented attributes of the nodes
        fComp1 = Aig_IsComplement(vSuper->pArray[i]);
        // determine the variable numbers
        Var1 = Aig_Regular(vSuper->pArray[i])->Data;
//        Var1 = (int)Aig_Regular(vSuper->pArray[i])->Id;

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
        fComp1 = Aig_IsComplement(vSuper->pArray[i]);
        // determine the variable numbers
        Var1 = Aig_Regular(vSuper->pArray[i])->Data;
//        Var1 = (int)Aig_Regular(vSuper->pArray[i])->Id;
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
int Aig_ClauseMux( solver * pSat, Aig_Node_t * pNode, Aig_Node_t * pNodeC, Aig_Node_t * pNodeT, Aig_Node_t * pNodeE, Vec_Int_t * vVars )
{
    int VarF, VarI, VarT, VarE, fCompT, fCompE;
//printf( "Adding mux %d.         %d\n", pNode->Id, (int)pSat->solver_stats.clauses );

    assert( !Aig_IsComplement( pNode ) );
    assert( Aig_NodeIsMuxType( pNode ) );
    // get the variable numbers
    VarF = pNode->Data;
    VarI = pNodeC->Data;
    VarT = Aig_Regular(pNodeT)->Data;
    VarE = Aig_Regular(pNodeE)->Data;
//    VarF = (int)pNode->Id;
//    VarI = (int)pNodeC->Id;
//    VarT = (int)Aig_Regular(pNodeT)->Id;
//    VarE = (int)Aig_Regular(pNodeE)->Id;

    // get the complementation flags
    fCompT = Aig_IsComplement(pNodeT);
    fCompE = Aig_IsComplement(pNodeE);

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
int Aig_ClauseCollectSupergate_rec( Aig_Node_t * pNode, Vec_Ptr_t * vSuper, int fFirst, int fStopAtMux )
{
    int RetValue1, RetValue2, i;
    // check if the node is visited
    if ( Aig_Regular(pNode)->fMarkB )
    {
        // check if the node occurs in the same polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == pNode )
                return 1;
        // check if the node is present in the opposite polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == Aig_Not(pNode) )
                return -1;
        assert( 0 );
        return 0;
    }
    // if the new node is complemented or a PI, another gate begins
    if ( !fFirst )
    if ( Aig_IsComplement(pNode) || !Aig_NodeIsAnd(pNode) || Aig_NodeRefs(pNode) > 1 || fStopAtMux && Aig_NodeIsMuxType(pNode) )
    {
        Vec_PtrPush( vSuper, pNode );
        Aig_Regular(pNode)->fMarkB = 1;
        return 0;
    }
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_NodeIsAnd(pNode) );
    // go through the branches
    RetValue1 = Aig_ClauseCollectSupergate_rec( Aig_NodeChild0(pNode), vSuper, 0, fStopAtMux );
    RetValue2 = Aig_ClauseCollectSupergate_rec( Aig_NodeChild1(pNode), vSuper, 0, fStopAtMux );
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
void Aig_ClauseCollectSupergate( Aig_Node_t * pNode, int fStopAtMux, Vec_Ptr_t * vNodes )
{
    int RetValue, i;
    assert( !Aig_IsComplement(pNode) );
    // collect the nodes in the implication supergate
    Vec_PtrClear( vNodes );
    RetValue = Aig_ClauseCollectSupergate_rec( pNode, vNodes, 1, fStopAtMux );
    assert( vNodes->nSize > 1 );
    // unmark the visited nodes
    for ( i = 0; i < vNodes->nSize; i++ )
        Aig_Regular((Aig_Node_t *)vNodes->pArray[i])->fMarkB = 0;
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
int Aig_ClauseCreateCnfInt( solver * pSat, Aig_Man_t * pNtk )
{
    Aig_Node_t * pNode, * pFanin, * pNodeC, * pNodeT, * pNodeE;
    Vec_Ptr_t * vNodes, * vSuper;
    Vec_Int_t * vVars;
    int i, k, fUseMuxes = 1;

    // start the data structures
    vNodes = Vec_PtrAlloc( 1000 );   // the nodes corresponding to vars in the solver
    vSuper = Vec_PtrAlloc( 100 );    // the nodes belonging to the given implication supergate
    vVars  = Vec_IntAlloc( 100 );    // the temporary array for variables in the clause

    // add the clause for the constant node
    pNode = Aig_ManConst1(pNtk);
    pNode->fMarkA = 1;
    pNode->Data = vNodes->nSize;
    Vec_PtrPush( vNodes, pNode );
    Aig_ClauseTriv( pSat, pNode, vVars );

    // collect the nodes that need clauses and top-level assignments
    Aig_ManForEachPo( pNtk, pNode, i )
    {
        // get the fanin
        pFanin = Aig_NodeFanin0(pNode);
        // create the node's variable
        if ( pFanin->fMarkA == 0 )
        {
            pFanin->fMarkA = 1;
            pFanin->Data = vNodes->nSize;
            Vec_PtrPush( vNodes, pFanin );
        }
        // add the trivial clause
        if ( !Aig_ClauseTriv( pSat, Aig_NodeChild0(pNode), vVars ) )
            return 0;
    }

    // add the clauses
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        assert( !Aig_IsComplement(pNode) );
        if ( !Aig_NodeIsAnd(pNode) )
            continue;
//printf( "%d ", pNode->Id );

        // add the clauses
        if ( fUseMuxes && Aig_NodeIsMuxType(pNode) )
        {
            pNode->pMan->nMuxes++;
            pNodeC = Aig_NodeRecognizeMux( pNode, &pNodeT, &pNodeE );
            Vec_PtrClear( vSuper );
            Vec_PtrPush( vSuper, pNodeC );
            Vec_PtrPush( vSuper, pNodeT );
            Vec_PtrPush( vSuper, pNodeE );
            // add the fanin nodes to explore
            Vec_PtrForEachEntry( vSuper, pFanin, k )
            {
                pFanin = Aig_Regular(pFanin);
                if ( pFanin->fMarkA == 0 )
                {
                    pFanin->fMarkA = 1;
                    pFanin->Data = vNodes->nSize;
                    Vec_PtrPush( vNodes, pFanin );
                }
            }
            // add the clauses
            if ( !Aig_ClauseMux( pSat, pNode, pNodeC, pNodeT, pNodeE, vVars ) )
                return 0;
        }
        else
        {
            // get the supergate
            Aig_ClauseCollectSupergate( pNode, fUseMuxes, vSuper );
            // add the fanin nodes to explore
            Vec_PtrForEachEntry( vSuper, pFanin, k )
            {
                pFanin = Aig_Regular(pFanin);
                if ( pFanin->fMarkA == 0 )
                {
                    pFanin->fMarkA = 1;
                    pFanin->Data = vNodes->nSize;
                    Vec_PtrPush( vNodes, pFanin );
                }
            }
            // add the clauses
            if ( vSuper->nSize == 0 )
            {
                if ( !Aig_ClauseTriv( pSat, Aig_Not(pNode), vVars ) )
                    return 0;
            }
            else
            {
                if ( !Aig_ClauseAnd( pSat, pNode, vSuper, vVars ) )
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
solver * Aig_ClauseCreateCnf( Aig_Man_t * pMan )
{
    solver * pSat;
    Aig_Node_t * pNode;
    int RetValue, i, clk = clock();
    // clean the marks
    Aig_ManForEachNode( pMan, pNode, i )
        pNode->fMarkA = 0, pNode->Data = -1;
    // create the solver
    pMan->nMuxes = 0;
    pSat = solver_new();
    RetValue = Aig_ClauseCreateCnfInt( pSat, pMan );
//    Asat_SolverWriteDimacs( pSat, "temp_sat.cnf", NULL, NULL, 1 );
    if ( RetValue == 0 )
    {
        solver_delete(pSat);
        Aig_ManForEachNode( pMan, pNode, i )
            pNode->fMarkA = 0;
        return NULL;
    }
    printf( "The number of MUXes detected = %d (%5.2f %% of logic).  ", 
        pNode->pMan->nMuxes, 300.0*pNode->pMan->nMuxes/Aig_ManNodeNum(pMan) );
    PRT( "Creating solver", clock() - clk );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Starts the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_ProofType_t Aig_ClauseSolverStart( Aig_Man_t * pMan )
{
    Aig_Node_t * pNode;
    int i;

    // make sure it has one PO
    if ( Aig_ManPoNum(pMan) != 1 )
    {
        printf( "The miter has other than 1 output.\n" );
        return AIG_PROOF_FAIL;
    }

    // get the solver
    assert( pMan->pSat == NULL );
    pMan->pSat = Aig_ClauseCreateCnf( pMan );
    if ( pMan->pSat == NULL )
        return AIG_PROOF_UNSAT;

    // get the variable mappings
    pMan->vVar2Sat = Vec_IntStart( Aig_ManNodeNum(pMan) );
    pMan->vSat2Var = Vec_IntStart( solver_nvars(pMan->pSat) );
    Aig_ManForEachNode( pMan, pNode, i )
    {
        Vec_IntWriteEntry( pMan->vVar2Sat, i, pNode->Data );
        if ( pNode->Data >= 0 ) Vec_IntWriteEntry( pMan->vSat2Var, pNode->Data, i );
    }
    // get the SAT var numbers of the primary inputs
    pMan->vPiSatNums = Vec_IntAlloc( Aig_ManPiNum(pMan) );
    Aig_ManForEachPi( pMan, pNode, i )
        Vec_IntPush( pMan->vPiSatNums, (pNode->Data >= 0)? pNode->Data : 0 );
    return AIG_PROOF_NONE;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


