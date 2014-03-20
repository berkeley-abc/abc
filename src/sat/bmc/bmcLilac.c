/**CFile****************************************************************

  FileName    [bmcLilac.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcLilac.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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
void Bmc_LilacUnfold( Gia_Man_t * pNew, Gia_Man_t * p, Vec_Int_t * vFFLits, int fPiReuse )
{
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ManRegNum(p) == Vec_IntSize(vFFLits) );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Vec_IntEntry(vFFLits, i);
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = fPiReuse ? Gia_ObjToLit(pNew, Gia_ManPi(pNew, Gia_ManPiNum(pNew)-Gia_ManPiNum(p)+i)) : Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        Vec_IntWriteEntry( vFFLits, i, Gia_ObjFanin0Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_LilacPart_rec( Gia_Man_t * pNew, Vec_Int_t * vSatMap, int iIdNew, Gia_Man_t * pPart, Vec_Int_t * vPartMap )
{
    Gia_Obj_t * pObj = Gia_ManObj( pNew, iIdNew ); 
    int iLitPart0, iLitPart1;
    if ( pObj->Value )
        return pObj->Value;
    if ( Vec_IntEntry(vSatMap, iIdNew) )
    {
        Vec_IntPush( vPartMap, iIdNew );
        return (pObj->Value = Gia_ManAppendCi(pPart));
    }
    iLitPart0 = Bmc_LilacPart_rec( pNew, vSatMap, Gia_ObjFaninId0(pObj, iIdNew), pPart, vPartMap );
    iLitPart1 = Bmc_LilacPart_rec( pNew, vSatMap, Gia_ObjFaninId1(pObj, iIdNew), pPart, vPartMap );
    iLitPart0 = Abc_LitNotCond( iLitPart0, Gia_ObjFaninC0(pObj) );
    iLitPart1 = Abc_LitNotCond( iLitPart1, Gia_ObjFaninC1(pObj) );
    Vec_IntPush( vPartMap, iIdNew );
    return (pObj->Value = Gia_ManAppendAnd( pPart, iLitPart0, iLitPart1 ));
}
Gia_Man_t * Bmc_LilacPart( Gia_Man_t * pNew, Vec_Int_t * vSatMap, Vec_Int_t * vMiters, Vec_Int_t * vPartMap )
{
    Gia_Man_t * pPart;
    int i, iLit, iLitPart;
    Gia_ManCleanValue( pNew );
    Vec_IntFillExtra( vSatMap, Gia_ManObjNum(pNew), -1 );
    pPart = Gia_ManStart( 1000 );
    pPart->pName = Abc_UtilStrsav( pNew->pName );
    Gia_ManConst0(pNew)->Value = 0;
    Vec_IntClear( vPartMap );
    Vec_IntForEachEntry( vMiters, iLit, i )
    {
        if ( iLit == -1 )
            continue;
        iLitPart = Bmc_LilacPart_rec( pNew, vSatMap, Abc_Lit2Var(iLit), pPart, vPartMap );
        Gia_ManAppendCo( pPart, Abc_LitNotCond(iLitPart, Abc_LitIsCompl(iLit)) );
    }
    assert( Gia_ManPoNum(pPart) > 0 );
    assert( Vec_IntSize(vPartMap) == Gia_ManObjNum(pPart) );
    return pPart;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_LilacPerform( Gia_Man_t * p, Vec_Int_t * vInit0, Vec_Int_t * vInit1, int nFrames, int fVerbose )
{
    int nSatVars = 1;
    int nTimeOut = 0;
    Vec_Int_t * vLits0, * vLits1, * vMiters, * vSatMap, * vPartMap;
    Gia_Man_t * pNew, * pPart;
    Gia_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    int i, f, status, iVar0, iVar1, iLit, iLit0, iLit1;
    int fChanges, RetValue = 1;

    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );

    pNew = Gia_ManStart( 10000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;

    vLits0 = Vec_IntAlloc( Gia_ManRegNum(p) );
    Vec_IntForEachEntry( vInit0, iLit, i )
        Vec_IntPush( vLits0, iLit < 2 ? iLit : Gia_ManAppendCi(pNew) );

    vLits1 = Vec_IntAlloc( Gia_ManRegNum(p) );
    Vec_IntForEachEntry( vInit1, iLit, i )
        Vec_IntPush( vLits1, iLit < 2 ? iLit : Gia_ManAppendCi(pNew) );

    vMiters  = Vec_IntAlloc( 1000 );
    vSatMap  = Vec_IntAlloc( 1000 );
    vPartMap = Vec_IntAlloc( 1000 );
    for ( f = 0; f < nFrames; f++ )
    {
        Bmc_LilacUnfold( pNew, p, vLits0, 0 );
        Bmc_LilacUnfold( pNew, p, vLits1, 1 );
        assert( Vec_IntSize(vLits0) == Vec_IntSize(vLits1) );
        Vec_IntClear( vMiters );
        Vec_IntForEachEntryTwo( vLits0, vLits1, iLit0, iLit1, i )
            if ( (iLit0 > 2 || iLit1 > 2) && iLit0 != iLit1 )
                Vec_IntPush( vMiters, Gia_ManHashXor(pNew, iLit0, iLit1) );
            else
                Vec_IntPush( vMiters, -1 );
        if ( Vec_IntSum(vMiters) + Vec_IntSize(vLits1) == 0 )
            continue;
        // create new part
        pPart = Bmc_LilacPart( pNew, vSatMap, vMiters, vPartMap );
        pCnf = Cnf_DeriveGiaRemapped( pPart );
        Cnf_DataLiftGia( pCnf, pPart, nSatVars );
        nSatVars += pCnf->nVars;
        sat_solver_setnvars( pSat, nSatVars );
        for ( i = 0; i < pCnf->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
                assert( 0 );
        // stitch the clauses
        Gia_ManForEachPi( pPart, pObj, i )
        {
            int iIdPart = Gia_ObjId(pPart, pObj);
            iVar0 = pCnf->pVarNums[iIdPart];
            iVar1 = Vec_IntEntry( vSatMap, Vec_IntEntry(vPartMap, iIdPart) );
            if ( iVar1 == -1 )
                continue;
            sat_solver_add_buffer( pSat, iVar0, iVar1, 0 );
        }
        // transfer variables
        Gia_ManForEachAnd( pPart, pObj, i )
            if ( pCnf->pVarNums[i] >= 0 )
                Vec_IntWriteEntry( vSatMap, Vec_IntEntry(vPartMap, i), pCnf->pVarNums[i] );
        Cnf_DataFree( pCnf );
        Gia_ManStop( pPart );
        // perform runs
        fChanges = 0;
        Vec_IntForEachEntry( vMiters, iLit, i )
        {
            if ( iLit == -1 )
                continue;
            status = sat_solver_solve( pSat, &iLit, &iLit + 1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            if ( status == l_True )
                continue;
            if ( status == l_Undef )
            {
                printf( "Timeout reached after %d seconds.  \n", nTimeOut );
                RetValue = 0;
                goto cleanup;
            }
            assert( status == l_False );
            iLit0 = Vec_IntEntry( vLits0, i );
            iLit1 = Vec_IntEntry( vLits1, i );
            assert( (iLit0 > 2 || iLit1 > 2) && iLit0 != iLit1 );
            if ( iLit1 > 2 )
                Vec_IntWriteEntry( vLits1, i, iLit0 );
            else
                Vec_IntWriteEntry( vLits0, i, iLit1 );
            iLit0 = Vec_IntEntry( vLits0, i );
            iLit1 = Vec_IntEntry( vLits1, i );
            assert( iLit0 == iLit1 );
            fChanges = 1;
        }
        if ( !fChanges )
        {
            printf( "Reached a fixed point after %d frames.  \n", f+1 );
            break;
        }
    }
cleanup:

    sat_solver_delete( pSat );
    Gia_ManStopP( &pNew );
    Vec_IntFree( vLits0 );
    Vec_IntFree( vLits1 );
    Vec_IntFree( vMiters );
    Vec_IntFree( vSatMap );
    Vec_IntFree( vPartMap );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_LilacTest( Gia_Man_t * p, Vec_Int_t * vInit, int nFrames, int fVerbose )
{
    Bmc_LilacPerform( p, vInit, vInit, nFrames, fVerbose );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

