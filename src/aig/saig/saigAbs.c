/**CFile****************************************************************

  FileName    [saigAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Proof-based abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

#include "cnf.h"
#include "satSolver.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates SAT solver for BMC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Saig_AbsCreateSolver( Cnf_Dat_t * pCnf, int nFrames )
{
    sat_solver * pSat;
    Vec_Int_t * vPoLits;
    Aig_Obj_t * pObjPo, * pObjLi, * pObjLo;
    int f, i, Lit, Lits[2], iVarOld, iVarNew;
    // start array of output literals
    vPoLits = Vec_IntAlloc( nFrames * Saig_ManPoNum(pCnf->pMan) );
    // create the SAT solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat ); 
    sat_solver_setnvars( pSat, pCnf->nVars * nFrames );

    // add clauses for the timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            {
                printf( "The BMC problem is trivially UNSAT.\n" );
                sat_solver_delete( pSat );
                Vec_IntFree( vPoLits );
                return NULL;
            }
        }
        // remember output literal
        Saig_ManForEachPo( pCnf->pMan, pObjPo, i )
            Vec_IntPush( vPoLits, toLit(pCnf->pVarNums[pObjPo->Id]) );
        // lift CNF to the next frame
        Cnf_DataLift( pCnf, pCnf->nVars );
    }
    // put CNF back to the original level
    Cnf_DataLift( pCnf, - pCnf->nVars * nFrames );

    // add auxiliary clauses (output, connectors, initial)
    // add output clause
    if ( !sat_solver_addclause( pSat, Vec_IntArray(vPoLits), Vec_IntArray(vPoLits) + Vec_IntSize(vPoLits) ) )
        assert( 0 );
    Vec_IntFree( vPoLits );
    // add connecting clauses
    for ( f = 0; f < nFrames; f++ )
    {
        // connect to the previous timeframe
        if ( f > 0 )
        {
            Saig_ManForEachLiLo( pCnf->pMan, pObjLi, pObjLo, i )
            {
                iVarOld = pCnf->pVarNums[pObjLi->Id] - pCnf->nVars;
                iVarNew = pCnf->pVarNums[pObjLo->Id];
                // add clauses connecting existing variables
                Lits[0] = toLitCond( iVarOld, 0 );
                Lits[1] = toLitCond( iVarNew, 1 );
                if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                    assert( 0 );
                Lits[0] = toLitCond( iVarOld, 1 );
                Lits[1] = toLitCond( iVarNew, 0 );
                if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                    assert( 0 );
            }
        }
        // lift CNF to the next frame
        Cnf_DataLift( pCnf, pCnf->nVars );
    }
    // put CNF back to the original level
    Cnf_DataLift( pCnf, - pCnf->nVars * nFrames );
    // add unit clauses
    Saig_ManForEachLo( pCnf->pMan, pObjLo, i )
    {
        assert( pCnf->pVarNums[pObjLo->Id] >= 0 );
        Lit = toLitCond( pCnf->pVarNums[pObjLo->Id], 1 );
        if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
            assert( 0 );
    }
    sat_solver_store_mark_roots( pSat ); 
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_AbsSolverUnsatCore( sat_solver * pSat, int nConfMax, int fVerbose )
{
    Vec_Int_t * vCore;
    void * pSatCnf; 
    Intp_Man_t * pManProof;
    int RetValue;
    // solve the problem
    RetValue = sat_solver_solve( pSat, NULL, NULL, (sint64)nConfMax, (sint64)0, (sint64)0, (sint64)0 );
    if ( RetValue == l_Undef )
    {
        printf( "Conflict limit is reached.\n" );
        return NULL;
    }
    if ( RetValue == l_True )
    {
        printf( "The BMC problem is SAT.\n" );
        return NULL;
    }
    if ( fVerbose )
        printf( "SAT solver returned UNSAT after %d conflicts.\n", pSat->stats.conflicts );
    assert( RetValue == l_False );
    pSatCnf = sat_solver_store_release( pSat ); 
    // derive the UNSAT core
    pManProof = Intp_ManAlloc();
    vCore = Intp_ManUnsatCore( pManProof, pSatCnf, fVerbose );
    Intp_ManFree( pManProof );
    Sto_ManFree( pSatCnf );
    return vCore;
}


/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_AbsCollectRegisters( Cnf_Dat_t * pCnf, int nFrames, Vec_Int_t * vCore )
{
    Aig_Obj_t * pObj;
    Vec_Int_t * vFlops;
    int * pVars, * pFlops;
    int i, iClause, iReg, * piLit;
    // mark register variables
    pVars = ALLOC( int, pCnf->nVars );
    for ( i = 0; i < pCnf->nVars; i++ )
        pVars[i] = -1;
    Saig_ManForEachLi( pCnf->pMan, pObj, i )
        pVars[ pCnf->pVarNums[pObj->Id] ] = i;
    Saig_ManForEachLo( pCnf->pMan, pObj, i )
        pVars[ pCnf->pVarNums[pObj->Id] ] = i;
    // mark used registers
    pFlops = CALLOC( int, Aig_ManRegNum(pCnf->pMan) );
    Vec_IntForEachEntry( vCore, iClause, i )
    {
        // skip auxiliary clauses
        if ( iClause >= pCnf->nClauses * nFrames )
            continue;
        // consider the clause
        iClause = iClause % pCnf->nClauses;
        for ( piLit = pCnf->pClauses[iClause]; piLit < pCnf->pClauses[iClause+1]; piLit++ )
        {
            iReg = pVars[ lit_var(*piLit) ];
            if ( iReg >= 0 )
                pFlops[iReg] = 1;
        }
    }
    // collect registers
    vFlops = Vec_IntAlloc( Aig_ManRegNum(pCnf->pMan) );
    for ( i = 0; i < Aig_ManRegNum(pCnf->pMan); i++ )
        if ( pFlops[i] )
            Vec_IntPush( vFlops, i );
    free( pFlops );
    free( pVars );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManProofAbstraction( Aig_Man_t * p, int nFrames, int nConfMax, int fVerbose )
{
    Aig_Man_t * pResult;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Vec_Int_t * vCore;
    Vec_Int_t * vFlops;
    int clk = clock();
    assert( Aig_ManRegNum(p) > 0 );
    Aig_ManSetPioNumbers( p );
    if ( fVerbose )
        printf( "Performing proof-based abstraction with %d frames and %d max conflicts.\n", nFrames, nConfMax );
    // create CNF for the AIG
    pCnf = Cnf_DeriveSimple( p, Aig_ManPoNum(p) );
    // create SAT solver for the unrolled AIG
    pSat = Saig_AbsCreateSolver( pCnf, nFrames );
    // compute UNSAT core
    vCore = Saig_AbsSolverUnsatCore( pSat, nConfMax, fVerbose );
    sat_solver_delete( pSat );
    if ( vCore == NULL )
    {
        Cnf_DataFree( pCnf );
        return NULL;
    }
    // collect registers
    vFlops = Saig_AbsCollectRegisters( pCnf, nFrames, vCore );
    Cnf_DataFree( pCnf );
    Vec_IntFree( vCore );
    if ( fVerbose )
    {
        printf( "The number of relevant registers is %d (out of %d).\n", Vec_IntSize(vFlops), Aig_ManRegNum(p) );
        PRT( "Time", clock() - clk );
    }
    // create the resulting AIG
    pResult = Saig_ManAbstraction( p, vFlops );
    Vec_IntFree( vFlops );
    return pResult;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


