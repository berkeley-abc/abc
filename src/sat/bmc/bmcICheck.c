/**CFile****************************************************************

  FileName    [bmcICheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Performs specialized check.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcICheck.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"

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
void Bmc_PerformICheck( Gia_Man_t * p, int nFramesMax, int nTimeOut, int fVerbose )
{
    Gia_Man_t * pMiter, * pTemp;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Vec_Int_t * vLits;
    Gia_Obj_t * pObj, * pObj0, * pObj1;
    int i, k, status, iVar0, iVar1, iVarOut;
    int nLits, * pLits;
    abctime clkStart = Abc_Clock();
    assert( nFramesMax > 0 );
    assert( Gia_ManRegNum(p) > 0 );

    // create miter
    pTemp = Gia_ManDup( p );
    pMiter = Gia_ManMiter( p, pTemp, 0, 1, 1, 0 );
    Gia_ManStop( pTemp );
    assert( Gia_ManPoNum(pMiter)  == 2 * Gia_ManPoNum(p) );
    assert( Gia_ManRegNum(pMiter) == 2 * Gia_ManRegNum(p) );
    // derive CNF
    pMiter = Jf_ManDeriveCnf( pTemp = pMiter, 0 );
    Gia_ManStop( pTemp );
    pCnf = (Cnf_Dat_t *)pMiter->pData; pMiter->pData = NULL;

    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, Gia_ManRegNum(p) + Gia_ManCoNum(p) + pCnf->nVars * (nFramesMax + 1) );
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );

    // load the last timeframe
    Cnf_DataLift( pCnf, Gia_ManRegNum(p) + Gia_ManCoNum(p) );
    // add one large OR clause
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_IntPush( vLits, Abc_Var2Lit(Gia_ManRegNum(p) + i, 0) );
    sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );
    // add XOR clauses
    Gia_ManForEachPo( p, pObj, i )
    {
        pObj0 = Gia_ManPo( pMiter, 2*i+0 );
        pObj1 = Gia_ManPo( pMiter, 2*i+1 );
        iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj0)];
        iVar1 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj1)];
        iVarOut = Gia_ManRegNum(p) + i;
        sat_solver_add_xor( pSat, iVar0, iVar1, iVarOut, 0 );
    }
    Gia_ManForEachRi( p, pObj, i )
    {
        pObj0 = Gia_ManRi( pMiter, i );
        pObj1 = Gia_ManRi( pMiter, i + Gia_ManRegNum(p) );
        iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj0)];
        iVar1 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj1)];
        iVarOut = Gia_ManRegNum(p) + Gia_ManPoNum(p) + i;
        sat_solver_add_xor( pSat, iVar0, iVar1, iVarOut, 0 );
    }
    // add timeframe clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );

    // add other timeframes
    printf( "Solving M-inductiveness for design %s with %d AND nodes and %d flip-flops:\n",
        Gia_ManName(p), Gia_ManAndNum(p), Gia_ManRegNum(p) );
    for ( k = 0; k < nFramesMax; k++ )
    {
        // collect variables of the RO nodes
        Vec_IntClear( vLits );
        Gia_ManForEachRo( pMiter, pObj, i )
            Vec_IntPush( vLits, pCnf->pVarNums[Gia_ObjId(pMiter, pObj)] );
        // lift CNF again
        Cnf_DataLift( pCnf, pCnf->nVars );
        // stitch the clauses
        Gia_ManForEachRi( pMiter, pObj, i )
        {
            iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj)];
            iVar1 = Vec_IntEntry( vLits, i );
            sat_solver_add_buffer( pSat, iVar0, iVar1, 0 );
        }
        // add equality clauses for the COs
        Gia_ManForEachPo( p, pObj, i )
        {
            pObj0 = Gia_ManPo( pMiter, 2*i+0 );
            pObj1 = Gia_ManPo( pMiter, 2*i+1 );
            iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj0)];
            iVar1 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj1)];
            sat_solver_add_buffer( pSat, iVar0, iVar1, 0 );
        }
        Gia_ManForEachRi( p, pObj, i )
        {
            pObj0 = Gia_ManRi( pMiter, i );
            pObj1 = Gia_ManRi( pMiter, i + Gia_ManRegNum(p) );
            iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj0)];
            iVar1 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj1)];
            sat_solver_add_buffer_enable( pSat, iVar0, iVar1, i, 0 );
        }
        // add timeframe clauses
        for ( i = 0; i < pCnf->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
                assert( 0 );

        // collect literals
        Vec_IntClear( vLits );
        for ( i = 0; i < Gia_ManRegNum(p); i++ )
            Vec_IntPush( vLits, Abc_Var2Lit(i, 0) );

        // call the SAT solver
    //    sat_solver_compress( pSat );
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        assert( status == l_False );

        // call analize_final
        nLits = sat_solver_final( pSat, &pLits );
        printf( "M = %d.  AIG =%8d.  SAT vars =%8d.  SAT conf =%8d.  S =%6d. (%6.2f %%)  ",
            k+1, (k+1) * Gia_ManAndNum(pMiter), 
            sat_solver_nvars(pSat), sat_solver_nconflicts(pSat),
            nLits, 100.0 * nLits / Gia_ManRegNum(p) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    }

    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Gia_ManStop( pMiter );
    Vec_IntFree( vLits );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

