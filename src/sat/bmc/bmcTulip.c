/**CFile****************************************************************

  FileName    [bmcTulip.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcTulip.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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
Gia_Man_t * Gia_ManTulipUnfold( Gia_Man_t * p, int nFrames, int fUseVars )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, f;
    pNew = Gia_ManStart( fUseVars * 2 * Gia_ManRegNum(p) + nFrames * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    // control/data variables
    Gia_ManForEachRo( p, pObj, i )
        Gia_ManAppendCi( pNew );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ManAppendCi( pNew );
    // build timeframes
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = fUseVars ? Gia_ManHashAnd(pNew, Gia_ManCiLit(pNew, i), Gia_ManCiLit(pNew, Gia_ManRegNum(p)+i)) : 0;
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ManForEachPi( p, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachAnd( p, pObj, i )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachRi( p, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        Gia_ManForEachRo( p, pObj, i )
            pObj->Value = Gia_ObjRoToRi(p, pObj)->Value;
    }
    Gia_ManForEachRi( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, pObj->Value );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    assert( Gia_ManPiNum(pNew) == 2 * Gia_ManRegNum(p) + nFrames * Gia_ManPiNum(p) );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManTulip( Gia_Man_t * p, int nFrames, int nTimeOut, int fVerbose )
{
    int nIterMax = 1000000;
    int i, iLit, Iter, status;
    int nLits, * pLits;
    abctime clkTotal = Abc_Clock();
    abctime clkSat = 0;
    Vec_Int_t * vLits, * vMap;
    sat_solver * pSat;
    Gia_Obj_t * pObj;
    Gia_Man_t * p0 = Gia_ManTulipUnfold( p, nFrames, 0 );
    Gia_Man_t * p1 = Gia_ManTulipUnfold( p, nFrames, 1 );
    Gia_Man_t * pM = Gia_ManMiter( p0, p1, 0, 0, 0, 0, 0 );
    Cnf_Dat_t * pCnf = Cnf_DeriveGiaRemapped( pM );
    Gia_ManStop( p0 );
    Gia_ManStop( p1 );
    assert( Gia_ManRegNum(p) > 0 );

    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );

    // add one large OR clause
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( pM, pObj, i )
        Vec_IntPush( vLits, Abc_Var2Lit(pCnf->pVarNums[Gia_ObjId(pM, pObj)], 0) );
    sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );

    // create assumptions
    Vec_IntClear( vLits );
    Gia_ManForEachPi( pM, pObj, i )
        if ( i == Gia_ManRegNum(p) )
            break;
        else
            Vec_IntPush( vLits, Abc_Var2Lit(pCnf->pVarNums[Gia_ObjId(pM, pObj)], 1) );

    if ( fVerbose )
    {
        printf( "Iter%6d : ",       0 );
        printf( "Var =%10d  ",      sat_solver_nvars(pSat) );
        printf( "Clause =%10d  ",   sat_solver_nclauses(pSat) );
        printf( "Conflict =%10d  ", sat_solver_nconflicts(pSat) );
        printf( "Subset =%6d  ",    Gia_ManRegNum(p) );
        Abc_PrintTime( 1, "Time", clkSat );
//      ABC_PRTr( "Solver time", clkSat );
    }
    for ( Iter = 0; Iter < nIterMax; Iter++ )
    {
        abctime clk = Abc_Clock();
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        clkSat += Abc_Clock() - clk;
        if ( status == l_Undef )
        {
//            if ( fVerbose )
//                printf( "\n" );
            printf( "Timeout reached after %d seconds and %d iterations.  ", nTimeOut, Iter );
            break;
        }
        if ( status == l_True )
        {
//            if ( fVerbose )
//                printf( "\n" );
            printf( "The problem is SAT after %d iterations.  ", Iter );
            break;
        }
        assert( status == l_False );
        nLits = sat_solver_final( pSat, &pLits );
        if ( fVerbose )
        {
            printf( "Iter%6d : ",       Iter+1 );
            printf( "Var =%10d  ",      sat_solver_nvars(pSat) );
            printf( "Clause =%10d  ",   sat_solver_nclauses(pSat) );
            printf( "Conflict =%10d  ", sat_solver_nconflicts(pSat) );
            printf( "Subset =%6d  ",    nLits );
            Abc_PrintTime( 1, "Time", clkSat );
//            ABC_PRTr( "Solver time", clkSat );
        }
        if ( Vec_IntSize(vLits) == nLits )
        {
//            if ( fVerbose )
//                printf( "\n" );
            printf( "Reached fixed point with %d entries after %d iterations.\n", Vec_IntSize(vLits), Iter+1 );
            break;
        }
        // collect used literals
        Vec_IntClear( vLits );
        for ( i = 0; i < nLits; i++ )
            Vec_IntPush( vLits, Abc_LitNot(pLits[i]) );
    }
    // create map
    vMap = Vec_IntStart( pCnf->nVars );
    Vec_IntForEachEntry( vLits, iLit, i )
        Vec_IntWriteEntry( vMap, Abc_Lit2Var(iLit), 1 );
    // create output
    Vec_IntClear( vLits );
    Gia_ManForEachPi( pM, pObj, i )
        if ( i == Gia_ManRegNum(p) )
            break;
        else if ( Vec_IntEntry( vMap, pCnf->pVarNums[Gia_ObjId(pM, pObj)] ) )
            Vec_IntPush( vLits, i );
    Vec_IntFree( vMap );

    // cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Gia_ManStop( pM );
    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    return vLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManTulipTest( Gia_Man_t * p, int nFrames, int nTimeOut, int fVerbose )
{
    Vec_Int_t * vRes;
    vRes = Gia_ManTulip( p, nFrames, nTimeOut, fVerbose );
    Vec_IntFree( vRes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

