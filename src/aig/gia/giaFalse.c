/**CFile****************************************************************

  FileName    [giaFalse.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Detection and elimination of false paths.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaFalse.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecQue.h"
#include "sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute slacks measured using the number of AIG levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManComputeSlacks( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, nLevels = Gia_ManLevelNum( p );
    Vec_Int_t * vLevelR = Gia_ManReverseLevel( p );
    Vec_Int_t * vSlacks = Vec_IntAlloc( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
        Vec_IntPush( vSlacks, nLevels - Gia_ObjLevelId(p, i) - Vec_IntEntry(vLevelR, i) );
    assert( Vec_IntSize(vSlacks) == Gia_ManObjNum(p) );
    Vec_IntFree( vLevelR );
    return vSlacks;
}

/**Function*************************************************************

  Synopsis    [Derive critical path by following minimum slacks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectPath_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSlacks, Vec_Int_t * vPath )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        int Slack = Vec_IntEntry(vSlacks, Gia_ObjId(p, pObj));
        int Slack0 = Vec_IntEntry(vSlacks, Gia_ObjFaninId0p(p, pObj));
        int Slack1 = Vec_IntEntry(vSlacks, Gia_ObjFaninId1p(p, pObj));
        assert( Slack == Slack0 || Slack == Slack1 );
        if ( Slack == Slack0 )
            Gia_ManCollectPath_rec( p, Gia_ObjFanin0(pObj), vSlacks, vPath );
        else 
            Gia_ManCollectPath_rec( p, Gia_ObjFanin1(pObj), vSlacks, vPath );
    }
    Vec_IntPush( vPath, Gia_ObjId(p, pObj) );
}
Vec_Int_t * Gia_ManCollectPath( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSlacks )
{
    Vec_Int_t * vPath = Vec_IntAlloc( p->nLevels );
    assert( Gia_ObjIsCo(pObj) );
    Gia_ManCollectPath_rec( p, Gia_ObjFanin0(pObj), vSlacks, vPath );
    return vPath;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckFalseOne( Gia_Man_t * p, int iOut, int nTimeOut, Vec_Int_t * vSlacks )
{
    sat_solver * pSat;
    Gia_Obj_t * pObj = Gia_ManCo( p, iOut );
    Vec_Int_t * vLits = Vec_IntAlloc( p->nLevels );
    Vec_Int_t * vPath = Gia_ManCollectPath( p, pObj, vSlacks );
    int i, Shift[2], status, nLits, * pLits;
    abctime clkStart = Abc_Clock();
    // collect objects and assign SAT variables
    int iFanin = Gia_ObjFaninId0p( p, pObj );
    Vec_Int_t * vObjs = Gia_ManCollectNodesCis( p, &iFanin, 1 );
    Gia_ManForEachObjVec( vObjs, p, pObj, i )
        pObj->Value = Vec_IntSize(vObjs) - 1 - i;
    // create SAT solver
    pSat = sat_solver_new();
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );
    sat_solver_setnvars( pSat, Vec_IntSize(vPath) + 2 * Vec_IntSize(vObjs) );
    Shift[0] = Vec_IntSize(vPath);
    Shift[1] = Vec_IntSize(vPath) + Vec_IntSize(vObjs);
    // add CNF for the path
    Gia_ManForEachObjVec( vPath, p, pObj, i )
    {
        sat_solver_add_xor( pSat, i, pObj->Value + Shift[0], pObj->Value + Shift[1], 0 );
        Vec_IntPush( vLits, Abc_Var2Lit(i, 0) );
    }
    // add CNF for the cone
    Gia_ManForEachObjVec( vObjs, p, pObj, i )
    {
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        sat_solver_add_and( pSat, pObj->Value + Shift[0], 
            Gia_ObjFanin0(pObj)->Value + Shift[0], Gia_ObjFanin1(pObj)->Value + Shift[0], 
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj) ); 
        sat_solver_add_and( pSat, pObj->Value + Shift[1], 
            Gia_ObjFanin0(pObj)->Value + Shift[1], Gia_ObjFanin1(pObj)->Value + Shift[1], 
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj) ); 
    }
    printf( "PO %6d : ", iOut );
    // call the SAT solver
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( status == l_Undef )
        printf( "Timeout reached after %d seconds. ", nTimeOut );
    else if ( status == l_True )
        printf( "There is no false path. " );
    else
    {
        assert( status == l_False );
        // call analize_final
        nLits = sat_solver_final( pSat, &pLits );
        printf( "False path contains %d nodes (out of %d):  ", nLits, Vec_IntSize(vLits) );
        printf( "top = %d  ", Vec_IntEntry(vPath, Abc_Lit2Var(pLits[0])) );
        for ( i = 0; i < nLits; i++ )
            printf( "%d ", Abc_Lit2Var(pLits[i]) );
        printf( "  " );
    }
    Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    sat_solver_delete( pSat );
    Vec_IntFree( vObjs );
    Vec_IntFree( vPath );
    Vec_IntFree( vLits );
}
void Gia_ManCheckFalse( Gia_Man_t * p, int nSlackMax, int nTimeOut )
{
    Vec_Que_t * vPrio;
    Vec_Flt_t * vWeights;
    Vec_Int_t * vSlacks;
    Gia_Obj_t * pObj;
    int i;
    vSlacks = Gia_ManComputeSlacks(p);
//Vec_IntPrint( vSlacks );
    // create PO weights
    vWeights = Vec_FltAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_FltPush( vWeights, p->nLevels - Vec_IntEntry(vSlacks, Gia_ObjId(p, pObj)) );
    // put POs into the queue
    vPrio = Vec_QueAlloc( Gia_ManCoNum(p) );
    Vec_QueSetPriority( vPrio, Vec_FltArrayP(vWeights) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_QuePush( vPrio, i );
    // work on each PO in the queue
    while ( Vec_QueTopPriority(vPrio) >= p->nLevels - nSlackMax )
        Gia_ManCheckFalseOne( p, Vec_QuePop(vPrio), nTimeOut, vSlacks );
    // cleanup
    Vec_IntFree( vSlacks );
    Vec_FltFree( vWeights );
    Vec_QueFree( vPrio );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckFalseTest( Gia_Man_t * p, int nSlackMax )
{
    Gia_ManCheckFalse( p, nSlackMax, 0 );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

