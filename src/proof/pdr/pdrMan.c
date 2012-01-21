/**CFile****************************************************************

  FileName    [pdrMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Manager procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrMan.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Man_t * Pdr_ManStart( Aig_Man_t * pAig, Pdr_Par_t * pPars, Vec_Int_t * vPrioInit )
{
    Pdr_Man_t * p;
    p = ABC_CALLOC( Pdr_Man_t, 1 );
    p->pPars    = pPars;
    p->pAig     = pAig;
    p->vSolvers = Vec_PtrAlloc( 0 );
    p->vClauses = Vec_VecAlloc( 0 );
    p->pQueue   = NULL;
    p->pOrder   = ABC_ALLOC( int, Aig_ManRegNum(pAig) );
    p->vActVars = Vec_IntAlloc( 256 );
    // internal use
    p->vPrio    = vPrioInit ? vPrioInit : Vec_IntStart( Aig_ManRegNum(pAig) );  // priority flops
    p->vLits    = Vec_IntAlloc( 100 );  // array of literals
    p->vCiObjs  = Vec_IntAlloc( 100 );  // cone leaves
    p->vCoObjs  = Vec_IntAlloc( 100 );  // cone roots
    p->vCiVals  = Vec_IntAlloc( 100 );  // cone leaf values
    p->vCoVals  = Vec_IntAlloc( 100 );  // cone root values
    p->vNodes   = Vec_IntAlloc( 100 );  // cone nodes
    p->vUndo    = Vec_IntAlloc( 100 );  // cone undos
    p->vVisits  = Vec_IntAlloc( 100 );  // intermediate
    p->vCi2Rem  = Vec_IntAlloc( 100 );  // CIs to be removed
    p->vRes     = Vec_IntAlloc( 100 );  // final result
    p->vSuppLits= Vec_IntAlloc( 100 );  // support literals
    p->pCubeJust= Pdr_SetAlloc( Saig_ManRegNum(pAig) );
    // additional AIG data-members
    if ( pAig->pFanData == NULL )
        Aig_ManFanoutStart( pAig );
    if ( pAig->pTerSimData == NULL )
        pAig->pTerSimData = ABC_CALLOC( unsigned, 1 + (Aig_ManObjNumMax(pAig) / 16) );
    p->timeStart = clock();
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManStop( Pdr_Man_t * p )
{
    Pdr_Set_t * pCla;
    sat_solver * pSat;
    int i, k;
    Aig_ManCleanMarkAB( p->pAig );
    if ( p->pPars->fVerbose ) 
    {
        printf( "Block =%5d  Oblig =%6d  Clause =%6d  Call =%6d (sat=%.1f%%)  Start =%4d\n", 
            p->nBlocks, p->nObligs, p->nCubes, p->nCalls, 100.0 * p->nCallsS / p->nCalls, p->nStarts );
        ABC_PRTP( "SAT solving", p->tSat,       p->tTotal );
        ABC_PRTP( "  unsat    ", p->tSatUnsat,  p->tTotal );
        ABC_PRTP( "  sat      ", p->tSatSat,    p->tTotal );
        ABC_PRTP( "Generalize ", p->tGeneral,   p->tTotal );
        ABC_PRTP( "Push clause", p->tPush,      p->tTotal );
        ABC_PRTP( "Ternary sim", p->tTsim,      p->tTotal );
        ABC_PRTP( "Containment", p->tContain,   p->tTotal );
        ABC_PRTP( "CNF compute", p->tCnf,       p->tTotal );
        ABC_PRTP( "TOTAL      ", p->tTotal,     p->tTotal );
    }
//    printf( "SS =%6d. SU =%6d. US =%6d. UU =%6d.\n", p->nCasesSS, p->nCasesSU, p->nCasesUS, p->nCasesUU );
    Vec_PtrForEachEntry( sat_solver *, p->vSolvers, pSat, i )
        sat_solver_delete( pSat );
    Vec_PtrFree( p->vSolvers );
    Vec_VecForEachEntry( Pdr_Set_t *, p->vClauses, pCla, i, k )
        Pdr_SetDeref( pCla );
    Vec_VecFree( p->vClauses );
    Pdr_QueueStop( p );
    ABC_FREE( p->pOrder );
    Vec_IntFree( p->vActVars );
    // static CNF
    Cnf_DataFree( p->pCnf1 );
    Vec_IntFreeP( &p->vVar2Reg );
    // dynamic CNF
    Cnf_DataFree( p->pCnf2 );
    if ( p->pvId2Vars )
    for ( i = 0; i < Aig_ManObjNumMax(p->pAig); i++ )
        Vec_IntFreeP( &p->pvId2Vars[i] );
    ABC_FREE( p->pvId2Vars );
    Vec_VecFreeP( (Vec_Vec_t **)&p->vVar2Ids );
    // internal use
    Vec_IntFreeP( &p->vPrio   );  // priority flops
    Vec_IntFree( p->vLits     );  // array of literals
    Vec_IntFree( p->vCiObjs   );  // cone leaves
    Vec_IntFree( p->vCoObjs   );  // cone roots
    Vec_IntFree( p->vCiVals   );  // cone leaf values
    Vec_IntFree( p->vCoVals   );  // cone root values
    Vec_IntFree( p->vNodes    );  // cone nodes
    Vec_IntFree( p->vUndo     );  // cone undos
    Vec_IntFree( p->vVisits   );  // intermediate
    Vec_IntFree( p->vCi2Rem   );  // CIs to be removed
    Vec_IntFree( p->vRes      );  // final result
    Vec_IntFree( p->vSuppLits );  // support literals
    ABC_FREE( p->pCubeJust );
    // additional AIG data-members
    if ( p->pAig->pFanData != NULL )
        Aig_ManFanoutStop( p->pAig );
    if ( p->pAig->pTerSimData != NULL )
        ABC_FREE( p->pAig->pTerSimData );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Derives counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Pdr_ManDeriveCex( Pdr_Man_t * p )
{
    Abc_Cex_t * pCex;
    Pdr_Obl_t * pObl;
    int i, f, Lit, nFrames = 0;
    // count the number of frames
    for ( pObl = p->pQueue; pObl; pObl = pObl->pNext )
        nFrames++;
    // create the counter-example
    pCex = Abc_CexAlloc( Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), nFrames );
    pCex->iPo    = (p->pPars->iOutput==-1)? 0 : p->pPars->iOutput;
    pCex->iFrame = nFrames-1;
    for ( pObl = p->pQueue, f = 0; pObl; pObl = pObl->pNext, f++ )
        for ( i = pObl->pState->nLits; i < pObl->pState->nTotal; i++ )
        {
            Lit = pObl->pState->Lits[i];
            if ( lit_sign(Lit) )
                continue;
            assert( lit_var(Lit) < pCex->nPis );
            Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + lit_var(Lit) );
        }
    assert( f == nFrames );
    return pCex;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

