/**CFile****************************************************************

  FileName    [sscSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT sweeping under constraints.]

  Synopsis    [SAT procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: sscSat.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sscInt.h"
#include "sat/cnf/cnf.h"
#include "aig/gia/giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the SAT solver for constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssc_ManStartSolver( Ssc_Man_t * p )
{
    Aig_Man_t * pAig = Gia_ManToAig( p->pFraig, 0 );
    Cnf_Dat_t * pDat = Cnf_Derive( pAig, 0 );
    sat_solver * pSat;
    int i, status;
    assert( p->pSat == NULL && p->vSatVars == NULL );
    assert( Aig_ManObjNumMax(pAig) == Gia_ManObjNum(p->pFraig) );
    Aig_ManStop( pAig );
//Cnf_DataWriteIntoFile( pDat, "dump.cnf", 1, NULL, NULL );
    // save variable mapping
    p->vSatVars = Vec_IntAllocArray( pDat->pVarNums, Gia_ManObjNum(p->pFraig) );  pDat->pVarNums = NULL;
    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pDat->nVars + 1000 );
    for ( i = 0; i < pDat->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pDat->pClauses[i], pDat->pClauses[i+1] ) )
        {
            Cnf_DataFree( pDat );
            sat_solver_delete( pSat );
            return;
        }
    }
    Cnf_DataFree( pDat );
    status = sat_solver_simplify( pSat );
    if ( status == 0 )
    {
        sat_solver_delete( pSat );
        return;
    }
    p->pSat = pSat;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ssc_ManFindPivotSat( Ssc_Man_t * p )
{
    Vec_Int_t * vInit;
    Gia_Obj_t * pObj;
    int i, status;
    status = sat_solver_solve( p->pSat, NULL, NULL, p->pPars->nBTLimit, 0, 0, 0 );
    if ( status != l_True ) // unsat or undec
        return NULL;
    vInit = Vec_IntAlloc( Gia_ManPiNum(p->pFraig) );
    Gia_ManForEachPi( p->pFraig, pObj, i )
        Vec_IntPush( vInit, sat_solver_var_value(p->pSat, Ssc_ObjSatNum(p, pObj)) );
    return vInit;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

