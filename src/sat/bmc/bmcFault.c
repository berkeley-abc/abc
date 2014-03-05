/**CFile****************************************************************

  FileName    [bmcFault.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Checking for functional faults.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcFault.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "aig/gia/giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cnf_Dat_t * Cnf_DeriveGiaRemapped( Gia_Man_t * p )
{
    Cnf_Dat_t * pCnf;
    Aig_Man_t * pAig = Gia_ManToAigSimple( p );
    pAig->nRegs = 0;
    pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    Aig_ManStop( pAig );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cnf_DataLiftGia( Cnf_Dat_t * p, Gia_Man_t * pGia, int nVarsPlus )
{
    Gia_Obj_t * pObj;
    int v;
    Gia_ManForEachObj( pGia, pObj, v )
        if ( p->pVarNums[Gia_ObjId(pGia, pObj)] >= 0 )
            p->pVarNums[Gia_ObjId(pGia, pObj)] += nVarsPlus;
    for ( v = 0; v < p->nLiterals; v++ )
        p->pClauses[0][v] += 2*nVarsPlus;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFaultUnfold( Gia_Man_t * p, int fUseMuxes )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, iThis;
    pNew = Gia_ManStart( (2 + 3 * fUseMuxes) * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    // add first timeframe
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    // add second timeframe
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ObjRoToRi(pNew, pObj)->Value;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iThis = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        if ( fUseMuxes )
            pObj->Value = Gia_ManHashMux( pNew, Gia_ManAppendCi(pNew), iThis, pObj->Value );
        else
            pObj->Value = iThis, Gia_ManAppendCi(pNew);
    }
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    assert( Gia_ManPiNum(pNew) == Gia_ManRegNum(p) + 2 * Gia_ManPiNum(p) + Gia_ManAndNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFaultCofactor( Gia_Man_t * p, Vec_Int_t * vValues )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
    {
        pObj->Value = Gia_ManAppendCi( pNew );
        if ( i < Vec_IntSize(vValues) )
            pObj->Value = Vec_IntEntry( vValues, i );
    }
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    assert( Gia_ManPiNum(pNew) == Gia_ManPiNum(p) );
    return pNew;

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFaultTest( Gia_Man_t * p )
{
    int nTimeOut = 0;
    int nIterMax = 100;
    int i, status;
    Vec_Int_t * vLits;
    sat_solver * pSat;
    Gia_Obj_t * pObj;
    Gia_Man_t * pC;
    Gia_Man_t * p0 = Gia_ManFaultUnfold( p, 0 );
    Gia_Man_t * p1 = Gia_ManFaultUnfold( p, 1 );
    Gia_Man_t * pM = Gia_ManMiter( p0, p1, 0, 0, 0, 0, 0 );
    Cnf_Dat_t * pCnf = Cnf_DeriveGiaRemapped( pM ), * pCnf2;
    Gia_ManStop( p0 );
    Gia_ManStop( p1 );

    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars * 10 );
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );
    // add timeframe clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );

    // add one large OR clause
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( pM, pObj, i )
        Vec_IntPush( vLits, Abc_Var2Lit(pCnf->pVarNums[Gia_ObjId(pM, pObj)], 0) );
    sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );

    // iterate through the test vectors
    for ( i = 0; i < nIterMax; i++ )
    {
        status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( status == l_Undef )
        {
            printf( "Timeout reached after %d seconds.\n", nTimeOut );
            break;
        }
        if ( status == l_False )
        {
            printf( "The problem is UNSAT.\n" );
            break;
        }
        assert( status == l_True );
        // collect SAT assignment
        Vec_IntClear( vLits );
        Gia_ManForEachPi( pM, pObj, i )
            if ( i < Gia_ManRegNum(p) + 2 * Gia_ManPiNum(p) )
                Vec_IntPush( vLits, sat_solver_var_value(pSat, pCnf->pVarNums[Gia_ObjId(pM, pObj)]) );
        // derive the cofactor
        pC = Gia_ManFaultCofactor( pM, vLits );
        // derive new CNF
        pCnf2 = Cnf_DeriveGiaRemapped( pC );
        Cnf_DataLiftGia( pCnf2, pC, pCnf->nVars );
        // add timeframe clauses
        for ( i = 0; i < pCnf2->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnf2->pClauses[i], pCnf2->pClauses[i+1] ) )
                assert( 0 );
        // add constraint clauses
        Gia_ManForEachPo( pC, pObj, i )
        {
            int Lit = Abc_Var2Lit(pCnf->pVarNums[Gia_ObjId(pC, pObj)], 1);
            if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
                assert( 0 );
        }
        // add connection clauses
        Gia_ManForEachPi( pM, pObj, i )
            if ( i >= Gia_ManRegNum(p) + 2 * Gia_ManPiNum(p) )
                sat_solver_add_buffer( pSat, pCnf->pVarNums[Gia_ObjId(pM, pObj)], pCnf2->pVarNums[Gia_ObjId(pC, Gia_ManPi(pC, i))], 0 );
        Cnf_DataFree( pCnf2 );
        Gia_ManStop( pC );
    }
    // cleanup
    Vec_IntFree( vLits );
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Gia_ManStop( pM );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

