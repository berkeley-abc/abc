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

static inline void   Gia_ParTestAlloc( Gia_Man_t * p, int nWords ) { assert( !p->pData ); p->pData = (unsigned *)ABC_ALLOC(word, 2*nWords*Gia_ManObjNum(p)); p->iData = nWords; }
static inline void   Gia_ParTestFree( Gia_Man_t * p )              { ABC_FREE( p->pData ); p->iData = 0;             }
static inline word * Gia_ParTestObj( Gia_Man_t * p, int Id )       { return (word *)p->pData + Id*(p->iData << 1);   }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManRoseInit( Gia_Man_t * p, Vec_Int_t * vInit )
{
    Gia_Obj_t * pObj;
    word * pData1, * pData0;
    int i, k;
    Gia_ManForEachRi( p, pObj, k )
    {
        pData0 = Gia_ParTestObj( p, Gia_ObjId(p, pObj) );
        pData1 = pData0 + p->iData;
        if ( Vec_IntEntry(vInit, k) == 0 ) // 0
            for ( i = 0; i < p->iData; i++ )
                pData0[i] = ~(word)0, pData1[i] = 0;
        else if ( Vec_IntEntry(vInit, k) == 1 ) // 1
            for ( i = 0; i < p->iData; i++ )
                pData0[i] = 0, pData1[i] = ~(word)0;
        else // if ( Vec_IntEntry(vInit, k) > 1 ) // X
            for ( i = 0; i < p->iData; i++ )
                pData0[i] = pData1[i] = 0;
    }
}
void Gia_ManRoseSimulateObj( Gia_Man_t * p, int Id )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Id );
    word * pData0, * pDataA0, * pDataB0;
    word * pData1, * pDataA1, * pDataB1;
    int i;
    if ( Gia_ObjIsAnd(pObj) )
    {
        pData0  = Gia_ParTestObj( p, Id );
        pData1  = pData0 + p->iData;
        if ( Gia_ObjFaninC0(pObj) )
        {
            pDataA1 = Gia_ParTestObj( p, Gia_ObjFaninId0(pObj, Id) );
            pDataA0 = pDataA1 + p->iData;
            if ( Gia_ObjFaninC1(pObj) )
            {
                pDataB1 = Gia_ParTestObj( p, Gia_ObjFaninId1(pObj, Id) );
                pDataB0 = pDataB1 + p->iData;
            }
            else 
            {
                pDataB0 = Gia_ParTestObj( p, Gia_ObjFaninId1(pObj, Id) );
                pDataB1 = pDataB0 + p->iData;
            }
        }
        else 
        {
            pDataA0 = Gia_ParTestObj( p, Gia_ObjFaninId0(pObj, Id) );
            pDataA1 = pDataA0 + p->iData;
            if ( Gia_ObjFaninC1(pObj) )
            {
                pDataB1 = Gia_ParTestObj( p, Gia_ObjFaninId1(pObj, Id) );
                pDataB0 = pDataB1 + p->iData;
            }
            else 
            {
                pDataB0 = Gia_ParTestObj( p, Gia_ObjFaninId1(pObj, Id) );
                pDataB1 = pDataB0 + p->iData;
            }
        }
        for ( i = 0; i < p->iData; i++ )
            pData0[i] = pDataA0[i] | pDataB0[i], pData1[i] = pDataA1[i] & pDataB1[i];
    }
    else if ( Gia_ObjIsCo(pObj) )
    {
        pData0  = Gia_ParTestObj( p, Id );
        pData1  = pData0 + p->iData;
        if ( Gia_ObjFaninC0(pObj) )
        {
            pDataA1 = Gia_ParTestObj( p, Gia_ObjFaninId0(pObj, Id) );
            pDataA0 = pDataA1 + p->iData;
        }
        else 
        {
            pDataA0 = Gia_ParTestObj( p, Gia_ObjFaninId0(pObj, Id) );
            pDataA1 = pDataA0 + p->iData;
        }
        for ( i = 0; i < p->iData; i++ )
            pData0[i] = pDataA0[i], pData1[i] = pDataA1[i];
    }
    else if ( Gia_ObjIsCi(pObj) )
    {
        if ( Gia_ObjIsPi(p, pObj) )
        {
            pData0  = Gia_ParTestObj( p, Id );
            pData1  = pData0 + p->iData;
            for ( i = 0; i < p->iData; i++ )
                pData0[i] = Gia_ManRandomW(0), pData1[i] = ~pData0[i];
        }
        else
        {
            int Id2 = Gia_ObjId(p, Gia_ObjRoToRi(p, pObj));
            pData0  = Gia_ParTestObj( p, Id );
            pData1  = pData0 + p->iData;
            pDataA0 = Gia_ParTestObj( p, Id2 );
            pDataA1 = pDataA0 + p->iData;
            for ( i = 0; i < p->iData; i++ )
                pData0[i] = pDataA0[i], pData1[i] = pDataA1[i];
        }
    }
    else if ( Gia_ObjIsConst0(pObj) )
    {
        pData0  = Gia_ParTestObj( p, Id );
        pData1  = pData0 + p->iData;
        for ( i = 0; i < p->iData; i++ )
            pData0[i] = ~(word)0, pData1[i] = 0;
    }
    else assert( 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManRoseHighestScore( Gia_Man_t * p, int * pCost )
{
    Gia_Obj_t * pObj;
    word * pData0, * pData1;
    int * pCounts, CountBest;
    int i, k, b, nPats, iPat;
    nPats = 64 * p->iData;
    pCounts = ABC_CALLOC( int, nPats );
    Gia_ManForEachRi( p, pObj, k )
    {
        pData0 = Gia_ParTestObj( p, Gia_ObjId(p, pObj) );
        pData1 = pData0 + p->iData;
        for ( i = 0; i < p->iData; i++ )
            for ( b = 0; b < 64; b++ )
                pCounts[64*i+b] += (((pData0[i] >> b) & 1) || ((pData1[i] >> b) & 1)); // binary
    }
    iPat = 0;
    CountBest = pCounts[0]; 
    for ( k = 1; k < nPats; k++ )
        if ( CountBest < pCounts[k] )
            CountBest = pCounts[k], iPat = k;
    *pCost = Gia_ManRegNum(p) - CountBest; // ternary
    ABC_FREE( pCounts );
    return iPat;
}
void Gia_ManRoseFindStarting( Gia_Man_t * p, Vec_Int_t * vInit, int iPat )
{
    Gia_Obj_t * pObj;
    word * pData0, * pData1;
    int i, k;
    Vec_IntClear( vInit );
    Gia_ManForEachRi( p, pObj, k )
    {
        pData0 = Gia_ParTestObj( p, Gia_ObjId(p, pObj) );
        pData1 = pData0 + p->iData;
        for ( i = 0; i < p->iData; i++ )
            assert( (pData0[i] & pData1[i]) == 0 );
        if ( Abc_InfoHasBit( (unsigned *)pData0, iPat ) )
            Vec_IntPush( vInit, 0 );
        else if ( Abc_InfoHasBit( (unsigned *)pData1, iPat ) )
            Vec_IntPush( vInit, 1 );
        else 
            Vec_IntPush( vInit, 2 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManRosePerform( Gia_Man_t * p, Vec_Int_t * vInit0, int nFrames, int nWords, int fVerbose )
{
    Vec_Int_t * vInit;
    Gia_Obj_t * pObj;
    int i, f, iPat, Cost, Cost0;
    abctime clk, clkTotal = Abc_Clock();
    Gia_ManRandomW( 1 );
    if ( fVerbose )
        printf( "Running with %d frames, %d words, and %sgiven init state.\n", nFrames, nWords, vInit0 ? "":"no " );
    vInit = Vec_IntDup(vInit0);
    Gia_ParTestAlloc( p, nWords );
    Gia_ManRoseInit( p, vInit );
    Cost0 = 0;
    Vec_IntForEachEntry( vInit, iPat, i )
        Cost0 += ((iPat >> 1) & 1);
    if ( fVerbose )
        printf( "Frame =%6d : Values =%6d (out of %6d)\n", 0, Cost0, Cost0 );
    for ( f = 0; f < nFrames; f++ )
    {
        clk = Abc_Clock();
        Gia_ManForEachObj( p, pObj, i )
            Gia_ManRoseSimulateObj( p, i );
        iPat = Gia_ManRoseHighestScore( p, &Cost );
        Gia_ManRoseFindStarting( p, vInit, iPat );
        Gia_ManRoseInit( p, vInit );
        if ( fVerbose )
            printf( "Frame =%6d : Values =%6d (out of %6d)   ", f+1, Cost, Cost0 );
        if ( fVerbose )
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Gia_ParTestFree( p );
    printf( "After %d frames, found a sequence to produce %d x-values (out of %d).  ", f, Cost, Gia_ManRegNum(p) );
    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
//    printf( "The resulting init state is invalid.\n" );
    Vec_IntFreeP( &vInit );
    return vInit;
}


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
Gia_Man_t * Gia_ManTulipUnfold( Gia_Man_t * p, int nFrames, int fUseVars, Vec_Int_t * vInit )
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
    assert( !vInit || Vec_IntSize(vInit) == Gia_ManRegNum(p) );
    Gia_ManForEachRo( p, pObj, i )
    {
        if ( Vec_IntEntry(vInit, i) == 0 )
            pObj->Value = fUseVars ? Gia_ManHashAnd(pNew, Gia_ManCiLit(pNew, i), Gia_ManCiLit(pNew, Gia_ManRegNum(p)+i)) : 0;
        else if ( Vec_IntEntry(vInit, i) == 1 )
            pObj->Value = fUseVars ? Gia_ManHashAnd(pNew, Gia_ManCiLit(pNew, i), Gia_ManCiLit(pNew, Gia_ManRegNum(p)+i)) : 1;
        else if ( Vec_IntEntry(vInit, i) == 2 )
            pObj->Value = Gia_ManHashAnd(pNew, Gia_ManCiLit(pNew, i), Gia_ManCiLit(pNew, Gia_ManRegNum(p)+i));
        else if ( Vec_IntEntry(vInit, i) == 3 )
            pObj->Value = Gia_ManHashAnd(pNew, Gia_ManCiLit(pNew, i), Gia_ManCiLit(pNew, Gia_ManRegNum(p)+i));
        else assert( 0 );
    }
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
Vec_Int_t * Gia_ManTulipPerform( Gia_Man_t * p, Vec_Int_t * vInit, int nFrames, int nTimeOut, int fVerbose )
{
    int nIterMax = 1000000;
    int i, iLit, Iter, status;
    int nLits, * pLits;
    abctime clkTotal = Abc_Clock();
    abctime clkSat = 0;
    Vec_Int_t * vLits, * vMap;
    sat_solver * pSat;
    Gia_Obj_t * pObj;
    Gia_Man_t * p0 = Gia_ManTulipUnfold( p, nFrames, 0, vInit );
    Gia_Man_t * p1 = Gia_ManTulipUnfold( p, nFrames, 1, vInit );
    Gia_Man_t * pM = Gia_ManMiter( p0, p1, 0, 0, 0, 0, 0 );
    Cnf_Dat_t * pCnf = Cnf_DeriveGiaRemapped( pM );
    Gia_ManStop( p0 );
    Gia_ManStop( p1 );
    assert( Gia_ManRegNum(p) > 0 );
    if ( fVerbose )
        printf( "Running with %d frames and %sgiven init state.\n", nFrames, vInit ? "":"no " );

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
        else if ( !(Vec_IntEntry(vInit, i) & 2) )
            Vec_IntPush( vLits, Abc_Var2Lit(pCnf->pVarNums[Gia_ObjId(pM, pObj)], 1) );

    if ( fVerbose )
    {
        printf( "Iter%6d : ",       0 );
        printf( "Var =%10d  ",      sat_solver_nvars(pSat) );
        printf( "Clause =%10d  ",   sat_solver_nclauses(pSat) );
        printf( "Conflict =%10d  ", sat_solver_nconflicts(pSat) );
        printf( "Subset =%6d  ",    Vec_IntSize(vLits) );
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
            printf( "Reached fixed point with %d entries after %d iterations.  ", Vec_IntSize(vLits), Iter+1 );
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
    Vec_IntFree( vLits );
    vLits = Vec_IntDup(vInit);
    Gia_ManForEachPi( pM, pObj, i )
        if ( i == Gia_ManRegNum(p) )
            break;
        else if ( !(Vec_IntEntry(vLits, i) & 2) && !Vec_IntEntry(vMap, pCnf->pVarNums[Gia_ObjId(pM, pObj)]) )
            Vec_IntWriteEntry( vLits, i, Vec_IntEntry(vLits, i) | 2 );
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
Vec_Int_t * Gia_ManTulipTest( Gia_Man_t * p, Vec_Int_t * vInit0, int nFrames, int nWords, int nTimeOut, int fSim, int fVerbose )
{
    Vec_Int_t * vRes, * vInit;
    if ( fSim )
    {
        vInit = Vec_IntAlloc(0); Vec_IntFill( vInit, Gia_ManRegNum(p), 2 );
        vRes = Gia_ManRosePerform( p, vInit, nFrames, nWords, fVerbose );
    }
    else
    {
        vInit = vInit0 ? vInit0 : Vec_IntStart( Gia_ManRegNum(p) );
        vRes = Gia_ManTulipPerform( p, vInit, nFrames, nTimeOut, fVerbose );
    }
    if ( vInit != vInit0 )
        Vec_IntFree( vInit );
    return vRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

