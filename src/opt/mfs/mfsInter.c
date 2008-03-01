/**CFile****************************************************************

  FileName    [mfsInter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures for computing resub function by interpolation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsInter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds constraints for the two-input AND-gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_MfsSatAddXor( sat_solver * pSat, int iVarA, int iVarB, int iVarC )
{
    lit Lits[3];

    Lits[0] = toLitCond( iVarA, 1 );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    Lits[0] = toLitCond( iVarA, 1 );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 0 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    Lits[0] = toLitCond( iVarA, 0 );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 0 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    Lits[0] = toLitCond( iVarA, 0 );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    return 1;
}

/**Function*************************************************************

  Synopsis    [Creates miter for checking resubsitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Abc_MfsCreateSolverResub( Mfs_Man_t * p, int * pCands, int nCands )
{
    sat_solver * pSat;
    Aig_Obj_t * pObjPo;
    int Lits[2], status, iVar, i, c;

    // get the literal for the output of F
    pObjPo = Aig_ManPo( p->pAigWin, Aig_ManPoNum(p->pAigWin) - Vec_PtrSize(p->vDivs) - 1 );
    Lits[0] = toLitCond( p->pCnf->pVarNums[pObjPo->Id], 0 );

    // collect the outputs of the divisors
    Vec_IntClear( p->vProjVars );
    Vec_PtrForEachEntryStart( p->pAigWin->vPos, pObjPo, i, Aig_ManPoNum(p->pAigWin) - Vec_PtrSize(p->vDivs) )
    {
        assert( p->pCnf->pVarNums[pObjPo->Id] >= 0 );
        Vec_IntPush( p->vProjVars, p->pCnf->pVarNums[pObjPo->Id] );
    }
    assert( Vec_IntSize(p->vProjVars) == Vec_PtrSize(p->vDivs) );

    // start the solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 2 * p->pCnf->nVars + Vec_PtrSize(p->vDivs) );
    if ( pCands )
        sat_solver_store_alloc( pSat );

    // load the first copy of the clauses
    for ( i = 0; i < p->pCnf->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, p->pCnf->pClauses[i], p->pCnf->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    // add the clause for the first output of F
    if ( !sat_solver_addclause( pSat, Lits, Lits+1 ) )
    {
        sat_solver_delete( pSat );
        return NULL;
    }

    // bookmark the clauses of A
    if ( pCands )
        sat_solver_store_mark_clauses_a( pSat );

    // transform the literals
    for ( i = 0; i < p->pCnf->nLiterals; i++ )
        p->pCnf->pClauses[0][i] += 2 * p->pCnf->nVars;
    // load the second copy of the clauses
    for ( i = 0; i < p->pCnf->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, p->pCnf->pClauses[i], p->pCnf->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    // transform the literals
    for ( i = 0; i < p->pCnf->nLiterals; i++ )
        p->pCnf->pClauses[0][i] -= 2 * p->pCnf->nVars;
    // add the clause for the second output of F
    Lits[0] = 2 * p->pCnf->nVars + lit_neg( Lits[0] );
    if ( !sat_solver_addclause( pSat, Lits, Lits+1 ) )
    {
        sat_solver_delete( pSat );
        return NULL;
    }

    if ( pCands )
    {
        // add relevant clauses for EXOR gates
        for ( c = 0; c < nCands; c++ )
        {
            // get the variable number of this divisor
            i = lit_var( pCands[c] ) - 2 * p->pCnf->nVars;
            // get the corresponding SAT variable
            iVar = Vec_IntEntry( p->vProjVars, i );
            // add the corresponding EXOR gate
            if ( !Abc_MfsSatAddXor( pSat, iVar, iVar + p->pCnf->nVars, 2 * p->pCnf->nVars + i ) )
            {
                sat_solver_delete( pSat );
                return NULL;
            }
            // add the corresponding clause
            if ( !sat_solver_addclause( pSat, pCands + c, pCands + c + 1 ) )
            {
                sat_solver_delete( pSat );
                return NULL;
            }
        }
        // bookmark the roots
        sat_solver_store_mark_roots( pSat );
    }
    else
    {
        // add the clauses for the EXOR gates - and remember their outputs
        Vec_IntForEachEntry( p->vProjVars, iVar, i )
        {
            if ( !Abc_MfsSatAddXor( pSat, iVar, iVar + p->pCnf->nVars, 2 * p->pCnf->nVars + i ) )
            {
                sat_solver_delete( pSat );
                return NULL;
            }
            Vec_IntWriteEntry( p->vProjVars, i, 2 * p->pCnf->nVars + i );
        }
        // simplify the solver
        status = sat_solver_simplify(pSat);
        if ( status == 0 )
        {
//            printf( "Abc_MfsCreateSolverResub(): SAT solver construction has failed. Skipping node.\n" );
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Performs interpolation.]

  Description [Derives the new function of the node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NtkMfsInterplate( Mfs_Man_t * p, int * pCands, int nCands )
{
    extern Hop_Obj_t * Kit_GraphToHop( Hop_Man_t * pMan, Kit_Graph_t * pGraph );

    sat_solver * pSat;
    Sto_Man_t * pCnf = NULL;
    unsigned * puTruth;
    Kit_Graph_t * pGraph;
    Hop_Obj_t * pFunc;
    int nFanins, status;
    int c, i, * pGloVars;

    // derive the SAT solver for interpolation
    pSat = Abc_MfsCreateSolverResub( p, pCands, nCands );

    // solve the problem
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)p->pPars->nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
    if ( status != l_False )
    {
        p->nTimeOuts++;
        return NULL;
    }
    // get the learned clauses
    pCnf = sat_solver_store_release( pSat );
    sat_solver_delete( pSat );

    // set the global variables
    pGloVars = Int_ManSetGlobalVars( p->pMan, nCands );
    for ( c = 0; c < nCands; c++ )
    {
        // get the variable number of this divisor
        i = lit_var( pCands[c] ) - 2 * p->pCnf->nVars;
        // get the corresponding SAT variable
        pGloVars[c] = Vec_IntEntry( p->vProjVars, i );
    }

    // derive the interpolant
    nFanins = Int_ManInterpolate( p->pMan, pCnf, 0, &puTruth );
    Sto_ManFree( pCnf );
    assert( nFanins == nCands );

    // transform interpolant into AIG
    pGraph = Kit_TruthToGraph( puTruth, nFanins, p->vMem );
    pFunc = Kit_GraphToHop( p->pNtk->pManFunc, pGraph );
    Kit_GraphFree( pGraph );
    return pFunc;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


