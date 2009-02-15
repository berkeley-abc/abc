/**CFile****************************************************************

  FileName    [cecSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [SAT solver calls.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec_ManSat_t * Cec_ManCreate( Aig_Man_t * pAig, Cec_ParSat_t * pPars )
{
    Cec_ManSat_t * p;
    // create interpolation manager
    p = ABC_ALLOC( Cec_ManSat_t, 1 );
    memset( p, 0, sizeof(Cec_ManSat_t) );
    p->pPars        = pPars;
    p->pAig         = pAig;
    // SAT solving
    p->nSatVars     = 1;
    p->pSatVars     = ABC_CALLOC( int, Aig_ManObjNumMax(pAig) );
    p->vUsedNodes   = Vec_PtrAlloc( 1000 );
    p->vFanins      = Vec_PtrAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManStop( Cec_ManSat_t * p )
{
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    Vec_PtrFree( p->vUsedNodes );
    Vec_PtrFree( p->vFanins );
    ABC_FREE( p->pSatVars );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Recycles the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSolverRecycle( Cec_ManSat_t * p )
{
    int Lit;
    if ( p->pSat )
    {
        Aig_Obj_t * pObj;
        int i;
        Vec_PtrForEachEntry( p->vUsedNodes, pObj, i )
            Cec_ObjSetSatNum( p, pObj, 0 );
        Vec_PtrClear( p->vUsedNodes );
//        memset( p->pSatVars, 0, sizeof(int) * Aig_ManObjNumMax(p->pAigTotal) );
        sat_solver_delete( p->pSat );
    }
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    // var 0 is not used
    // var 1 is reserved for const1 node - add the clause
    p->nSatVars = 1;
//    p->nSatVars = 0;
    Lit = toLit( p->nSatVars );
    if ( p->pPars->fPolarFlip )
        Lit = lit_neg( Lit );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    Cec_ObjSetSatNum( p, Aig_ManConst1(p->pAig), p->nSatVars++ );

    p->nRecycles++;
    p->nCallsSince = 0;
}

/**Function*************************************************************

  Synopsis    [Runs equivalence test for the two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSatCheckNode( Cec_ManSat_t * p, Aig_Obj_t * pNode )
{
    int nBTLimit = p->pPars->nBTLimit;
    int Lit, RetValue, status, clk;

    // sanity checks
    assert( !Aig_IsComplement(pNode) );

    p->nCallsSince++;  // experiment with this!!!
    
    // check if SAT solver needs recycling
    if ( p->pSat == NULL || 
        (p->pPars->nSatVarMax && 
         p->nSatVars > p->pPars->nSatVarMax && 
         p->nCallsSince > p->pPars->nCallsRecycle) )
        Cec_ManSatSolverRecycle( p );

    // if the nodes do not have SAT variables, allocate them
    Cec_CnfNodeAddToSolver( p, pNode );

    // propage unit clauses
    if ( p->pSat->qtail != p->pSat->qhead )
    {
        status = sat_solver_simplify(p->pSat);
        assert( status != 0 );
        assert( p->pSat->qtail == p->pSat->qhead );
    }

    // solve under assumptions
    // A = 1; B = 0     OR     A = 1; B = 1 
    Lit = toLitCond( Cec_ObjSatNum(p,pNode), pNode->fPhase );
    if ( p->pPars->fPolarFlip )
    {
        if ( pNode->fPhase )  Lit = lit_neg( Lit );
    }
//Sat_SolverWriteDimacs( p->pSat, "temp.cnf", pLits, pLits + 2, 1 );
clk = clock();
    RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, 
        (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( RetValue == l_False )
    {
p->timeSatUnsat += clock() - clk;
        Lit = lit_neg( Lit );
        RetValue = sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
        assert( RetValue );
        p->timeSatUnsat++;
        return 1;
    }
    else if ( RetValue == l_True )
    {
p->timeSatSat += clock() - clk;
        p->timeSatSat++;
        return 0;
    }
    else // if ( RetValue == l_Undef )
    {
p->timeSatUndec += clock() - clk;
        p->timeSatUndec++;
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec_MtrStatus_t Cec_SatSolveOutputs( Aig_Man_t * pAig, Cec_ParSat_t * pPars )
{
    Bar_Progress_t * pProgress = NULL;
    Cec_MtrStatus_t Status;
    Cec_ManSat_t * p;
    Aig_Obj_t * pObj;
    int i, status;
    Status = Cec_MiterStatus( pAig );
    p = Cec_ManCreate( pAig, pPars );
    pProgress = Bar_ProgressStart( stdout, Aig_ManPoNum(pAig) );
    Aig_ManForEachPo( pAig, pObj, i )
    {
        Bar_ProgressUpdate( pProgress, i, "SAT..." );
        if ( Cec_OutputStatus(pAig, pObj) )
            continue;
        status = Cec_ManSatCheckNode( p, Aig_ObjFanin0(pObj) );
        if ( status == 1 )
        {
            Status.nUndec--, Status.nUnsat++;
            Aig_ObjPatchFanin0( pAig, pObj, Aig_ManConst0(pAig) );
        }
        if ( status == 0 )
        {
            Status.nUndec--, Status.nSat++;
            Aig_ObjPatchFanin0( pAig, pObj, Aig_ManConst1(pAig) );
        }
        if ( status == -1 )
            continue;
        // save the pattern (if it is first)
        if ( Status.iOut == -1 )
        {
        }
        // quit if at least one of them is solved
        if ( status == 0 && pPars->fFirstStop )
            break;
    }
    Aig_ManCleanup( pAig );
    Bar_ProgressStop( pProgress );
    printf( "    Confs = %8d.  Recycles = %6d.\n", p->pPars->nBTLimit, p->nRecycles );
    Cec_ManStop( p );
    return Status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


