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
sat_solver * Bmc_DeriveSolver( Gia_Man_t * p, Gia_Man_t * pMiter, Cnf_Dat_t * pCnf, int nFramesMax, int nTimeOut, int fVerbose )
{
    sat_solver * pSat;
    Vec_Int_t * vLits;
    Gia_Obj_t * pObj, * pObj0, * pObj1;
    int i, k, iVar0, iVar1, iVarOut;
    int VarShift = 0;

    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, Gia_ManRegNum(p) + Gia_ManCoNum(p) + pCnf->nVars * (nFramesMax + 1) );
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );

    // add one large OR clause
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_IntPush( vLits, Abc_Var2Lit(Gia_ManRegNum(p) + i, 0) );
    sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );

    // load the last timeframe
    Cnf_DataLiftGia( pCnf, pMiter, Gia_ManRegNum(p) + Gia_ManCoNum(p) );
    VarShift += Gia_ManRegNum(p) + Gia_ManCoNum(p);

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
        sat_solver_add_xor_and( pSat, iVarOut, iVar0, iVar1, i );
    }
    // add timeframe clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );

    // add other timeframes
    for ( k = 0; k < nFramesMax; k++ )
    {
        // collect variables of the RO nodes
        Vec_IntClear( vLits );
        Gia_ManForEachRo( pMiter, pObj, i )
            Vec_IntPush( vLits, pCnf->pVarNums[Gia_ObjId(pMiter, pObj)] );
        // lift CNF again
        Cnf_DataLiftGia( pCnf, pMiter, pCnf->nVars );
        VarShift += pCnf->nVars;
        // stitch the clauses
        Gia_ManForEachRi( pMiter, pObj, i )
        {
            iVar0 = pCnf->pVarNums[Gia_ObjId(pMiter, pObj)];
            iVar1 = Vec_IntEntry( vLits, i );
            if ( iVar1 == -1 )
                continue;
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
    }
//    sat_solver_compress( pSat );
    Cnf_DataLiftGia( pCnf, pMiter, -VarShift );
    Vec_IntFree( vLits );
    return pSat;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_PerformICheck( Gia_Man_t * p, int nFramesMax, int nTimeOut, int fEmpty, int fVerbose )
{
    int fUseOldCnf = 0;
    Gia_Man_t * pMiter, * pTemp;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Vec_Int_t * vLits, * vUsed;
    int i, status, Lit;
    int nLitsUsed, nLits, * pLits;
    abctime clkStart = Abc_Clock();
    assert( nFramesMax > 0 );
    assert( Gia_ManRegNum(p) > 0 );

    printf( "Solving M-inductiveness for design %s with %d AND nodes and %d flip-flops:\n",
        Gia_ManName(p), Gia_ManAndNum(p), Gia_ManRegNum(p) );

    // create miter
    pTemp = Gia_ManDup( p );
    pMiter = Gia_ManMiter( p, pTemp, 0, 1, 1, 0, 0 );
    Gia_ManStop( pTemp );
    assert( Gia_ManPoNum(pMiter)  == 2 * Gia_ManPoNum(p) );
    assert( Gia_ManRegNum(pMiter) == 2 * Gia_ManRegNum(p) );
    // derive CNF
    if ( fUseOldCnf )
        pCnf = Cnf_DeriveGiaRemapped( pMiter );
    else
    {
        pMiter = Jf_ManDeriveCnf( pTemp = pMiter, 0 );
        Gia_ManStop( pTemp );
        pCnf = (Cnf_Dat_t *)pMiter->pData; pMiter->pData = NULL;
    }

    // collect positive literals
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    for ( i = 0; i < Gia_ManRegNum(p); i++ )
        Vec_IntPush( vLits, Abc_Var2Lit(i, fEmpty) );

    // iteratively compute a minimal M-inductive set of next-state functions
    nLitsUsed = fEmpty ? 0 : Vec_IntSize(vLits);
    vUsed = Vec_IntAlloc( Vec_IntSize(vLits) );
    while ( 1 )
    {
        int fChanges = 0;
        // derive SAT solver        
        pSat = Bmc_DeriveSolver( p, pMiter, pCnf, nFramesMax, nTimeOut, fVerbose );
//        sat_solver_bookmark( pSat );
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( status == l_Undef )
        {
            printf( "Timeout reached after %d seconds.\n", nTimeOut );
            break;
        }
        if ( status == l_True )
        {
            printf( "The problem is satisfiable (the current set is not M-inductive).\n" );
            break;
        }
        assert( status == l_False );
        // call analize_final
        nLits = sat_solver_final( pSat, &pLits );
        // mark used literals
        Vec_IntFill( vUsed, Vec_IntSize(vLits), 0 );
        for ( i = 0; i < nLits; i++ )
            Vec_IntWriteEntry( vUsed, Abc_Lit2Var(pLits[i]), 1 );

        // check if there are any positive unused
        Vec_IntForEachEntry( vLits, Lit, i )
        {
            assert( i == Abc_Lit2Var(Lit) );
            if ( Abc_LitIsCompl(Lit) )
                continue;
            if ( Vec_IntEntry(vUsed, i) )
                continue;
            // positive literal became unused
            Vec_IntWriteEntry( vLits, i, Abc_LitNot(Lit) );
            nLitsUsed--;
            fChanges = 1;
        }
        // report the results
        printf( "M =%4d :  AIG =%8d.  SAT vars =%8d.  SAT conf =%8d.  S =%6d. (%6.2f %%)  ",
            nFramesMax, (nFramesMax+1) * Gia_ManAndNum(pMiter), 
            Gia_ManRegNum(p) + Gia_ManCoNum(p) + sat_solver_nvars(pSat), 
            sat_solver_nconflicts(pSat), nLitsUsed, 100.0 * nLitsUsed / Gia_ManRegNum(p) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
        // count the number of negative literals
        sat_solver_delete( pSat );
        if ( !fChanges || fEmpty )
            break;
//        break;
//        sat_solver_rollback( pSat );
    }
    Cnf_DataFree( pCnf );
    Gia_ManStop( pMiter );
    Vec_IntFree( vLits );
    Vec_IntFree( vUsed );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_PerformISearchOne( Gia_Man_t * p, int nFramesMax, int nTimeOut, int fReverse, int fVerbose, Vec_Int_t * vLits )
{
    int fUseOldCnf = 0;
    Gia_Man_t * pMiter, * pTemp;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
//    Vec_Int_t * vLits;
    int i, Iter, status;
    int nLitsUsed;
    abctime clkStart = Abc_Clock();
    assert( nFramesMax > 0 );
    assert( Gia_ManRegNum(p) > 0 );

    // create miter
    pTemp = Gia_ManDup( p );
    pMiter = Gia_ManMiter( p, pTemp, 0, 1, 1, 0, 0 );
    Gia_ManStop( pTemp );
    assert( Gia_ManPoNum(pMiter)  == 2 * Gia_ManPoNum(p) );
    assert( Gia_ManRegNum(pMiter) == 2 * Gia_ManRegNum(p) );
    // derive CNF
    if ( fUseOldCnf )
        pCnf = Cnf_DeriveGiaRemapped( pMiter );
    else
    {
        pMiter = Jf_ManDeriveCnf( pTemp = pMiter, 0 );
        Gia_ManStop( pTemp );
        pCnf = (Cnf_Dat_t *)pMiter->pData; pMiter->pData = NULL;
    }
/*
    // collect positive literals
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    for ( i = 0; i < Gia_ManRegNum(p); i++ )
        Vec_IntPush( vLits, Abc_Var2Lit(i, 0) );
*/
    // derive SAT solver        
    pSat = Bmc_DeriveSolver( p, pMiter, pCnf, nFramesMax, nTimeOut, fVerbose );
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( status == l_True )
    {
        printf( "I = %4d :  ", nFramesMax );
        printf( "Problem is satisfiable.\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnf );
        Gia_ManStop( pMiter );
        return;
    }
    assert( status == l_False );

    // count the number of positive literals
    nLitsUsed = 0;
    for ( i = 0; i < Gia_ManRegNum(p); i++ )
        if ( !Abc_LitIsCompl(Vec_IntEntry(vLits, i)) )
            nLitsUsed++;

    // try removing variables
    for ( Iter = 0; Iter < Gia_ManRegNum(p); Iter++ )
    {
        i = fReverse ? Gia_ManRegNum(p) - 1 - Iter : Iter;
        if ( Abc_LitIsCompl(Vec_IntEntry(vLits, i)) )
            continue;
        Vec_IntWriteEntry( vLits, i, Abc_LitNot(Vec_IntEntry(vLits, i)) );
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( status == l_Undef )
        {
            printf( "Timeout reached after %d seconds.\n", nTimeOut );
            break;
        }
        if ( status == l_True )
            Vec_IntWriteEntry( vLits, i, Abc_LitNot(Vec_IntEntry(vLits, i)) );
        else if ( status == l_False )
            nLitsUsed--;
        else assert( 0 );
        // report the results
        //printf( "Round %d:  ", o );
        printf( "I = %4d :  AIG =%8d.  SAT vars =%8d.  SAT conf =%8d.  S =%6d. (%6.2f %%)  ",
            i, (nFramesMax+1) * Gia_ManAndNum(pMiter), 
            Gia_ManRegNum(p) + Gia_ManCoNum(p) + sat_solver_nvars(pSat), 
            sat_solver_nconflicts(pSat), nLitsUsed, 100.0 * nLitsUsed / Gia_ManRegNum(p) );
        ABC_PRTr( "Time", Abc_Clock() - clkStart );
        fflush( stdout );
    }
    // report the results
    //printf( "Round %d:  ", o );
    printf( "M = %4d :  AIG =%8d.  SAT vars =%8d.  SAT conf =%8d.  S =%6d. (%6.2f %%)  ",
        nFramesMax, (nFramesMax+1) * Gia_ManAndNum(pMiter), 
        Gia_ManRegNum(p) + Gia_ManCoNum(p) + sat_solver_nvars(pSat), 
        sat_solver_nconflicts(pSat), nLitsUsed, 100.0 * nLitsUsed / Gia_ManRegNum(p) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    fflush( stdout );

    // cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Gia_ManStop( pMiter );
//    Vec_IntFree( vLits );
}
Vec_Int_t * Bmc_PerformISearch( Gia_Man_t * p, int nFramesMax, int nTimeOut, int fReverse, int fDump, int fVerbose )
{
    Vec_Int_t * vLits, * vFlops;
    int i, f;
    printf( "Solving M-inductiveness for design %s with %d AND nodes and %d flip-flops:\n",
        Gia_ManName(p), Gia_ManAndNum(p), Gia_ManRegNum(p) );
    fflush( stdout );

    // collect positive literals
    vLits = Vec_IntAlloc( Gia_ManCoNum(p) );
    for ( i = 0; i < Gia_ManRegNum(p); i++ )
        Vec_IntPush( vLits, Abc_Var2Lit(i, 0) );

    for ( f = 1; f <= nFramesMax; f++ )
        Bmc_PerformISearchOne( p, f, nTimeOut, fReverse, fVerbose, vLits );

    // dump the numbers of the flops
    if ( fDump )
    {
        int nLitsUsed = 0;
        for ( i = 0; i < Gia_ManRegNum(p); i++ )
            if ( !Abc_LitIsCompl(Vec_IntEntry(vLits, i)) )
                nLitsUsed++;
        printf( "The set contains %d (out of %d) next-state functions with 0-based numbers:\n", nLitsUsed, Gia_ManRegNum(p) );
        for ( i = 0; i < Gia_ManRegNum(p); i++ )
            if ( !Abc_LitIsCompl(Vec_IntEntry(vLits, i)) )
                printf( "%d ", i );
        printf( "\n" );
    }       
    // save flop indexes
    vFlops = Vec_IntAlloc( Gia_ManRegNum(p) );
    for ( i = 0; i < Gia_ManRegNum(p); i++ )
        if ( !Abc_LitIsCompl(Vec_IntEntry(vLits, i)) )
            Vec_IntPush( vFlops, 1 );
        else
            Vec_IntPush( vFlops, 0 );
    Vec_IntFree( vLits );
    return vFlops;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

