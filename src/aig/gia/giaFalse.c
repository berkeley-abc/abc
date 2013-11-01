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
#include "misc/vec/vecWec.h"
#include "sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reconstruct the AIG after detecting false paths.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFalseRebuildOne( Gia_Man_t * pNew, Gia_Man_t * p, Vec_Int_t * vHook, int fVerbose, int fVeryVerbose )
{
    Gia_Obj_t * pObj, * pPrev = NULL; 
    int i, iObjValue, iPrevValue = -1;
    if ( fVerbose )
    {
        printf( "Eliminating path: " );
        Vec_IntPrint( vHook );
    }
    Gia_ManForEachObjVec( vHook, p, pObj, i )
    {
        if ( fVeryVerbose )
            Gia_ObjPrint( p, pObj );
        iObjValue = pObj->Value;
        pObj->Value = i ? Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj)) : 0;
        if ( pPrev )
            pPrev->Value = iPrevValue;
        iPrevValue = iObjValue;
        pPrev = pObj;
    }
}
Gia_Man_t * Gia_ManFalseRebuild( Gia_Man_t * p, Vec_Wec_t * vHooks, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, Counter = 0;
    pNew = Gia_ManStart( 4 * Gia_ManObjNum(p) / 3 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( Vec_WecLevelSize(vHooks, i) > 0 )
            {
                if ( fVerbose )
                    printf( "Path %d : ", Counter++ );
                Gia_ManFalseRebuildOne( pNew, p, Vec_WecEntry(vHooks, i), fVerbose, fVeryVerbose );
            }
            else
                pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derive critical path by following minimum slacks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectPath_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPath )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        if ( Gia_ObjLevel(p, Gia_ObjFanin0(pObj)) > Gia_ObjLevel(p, Gia_ObjFanin1(pObj)) )
            Gia_ManCollectPath_rec( p, Gia_ObjFanin0(pObj), vPath );
        else if ( Gia_ObjLevel(p, Gia_ObjFanin0(pObj)) < Gia_ObjLevel(p, Gia_ObjFanin1(pObj)) )
            Gia_ManCollectPath_rec( p, Gia_ObjFanin1(pObj), vPath );
//        else if ( rand() & 1 )
//            Gia_ManCollectPath_rec( p, Gia_ObjFanin0(pObj), vPath );
        else
            Gia_ManCollectPath_rec( p, Gia_ObjFanin1(pObj), vPath );
    }
    Vec_IntPush( vPath, Gia_ObjId(p, pObj) );
}
Vec_Int_t * Gia_ManCollectPath( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Vec_Int_t * vPath = Vec_IntAlloc( p->nLevels );
    Gia_ManCollectPath_rec( p, Gia_ObjFanin0(pObj), vPath );
    return vPath;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckFalseOne( Gia_Man_t * p, int iOut, int nTimeOut, Vec_Wec_t * vHooks, int fVerbose, int fVeryVerbose )
{
    sat_solver * pSat;
    Gia_Obj_t * pObj;
    Gia_Obj_t * pPivot = Gia_ManCo( p, iOut );
    Vec_Int_t * vLits = Vec_IntAlloc( p->nLevels );
    Vec_Int_t * vPath = Gia_ManCollectPath( p, pPivot );
    int nLits = 0, * pLits = NULL;
    int i, Shift[2], status;
    abctime clkStart = Abc_Clock();
    // collect objects and assign SAT variables
    int iFanin = Gia_ObjFaninId0p( p, pPivot );
    Vec_Int_t * vObjs = Gia_ManCollectNodesCis( p, &iFanin, 1 );
    Gia_ManForEachObjVec( vObjs, p, pObj, i )
        pObj->Value = Vec_IntSize(vObjs) - 1 - i;
    assert( Gia_ObjIsCo(pPivot) );
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
    // call the SAT solver
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( status == l_False )
    {
        int iBeg, iEnd;
        nLits = sat_solver_final( pSat, &pLits );
        iBeg  = Abc_Lit2Var(pLits[nLits-1]);
        iEnd  = Abc_Lit2Var(pLits[0]);
        if ( iEnd - iBeg < 20 )
        {
            // check if nodes on the path are already used
            for ( i = iBeg; i <= iEnd; i++ )
                if ( Vec_WecLevelSize(vHooks, Vec_IntEntry(vPath, i)) > 0 )
                    break;
            if ( i > iEnd )
            {
                Vec_Int_t * vHook = Vec_WecEntry(vHooks, Vec_IntEntry(vPath, iEnd));
                for ( i = iBeg; i <= iEnd; i++ )
                    Vec_IntPush( vHook, Vec_IntEntry(vPath, i) );
            }
        }
    }
    if ( fVerbose )
    {
        printf( "PO %6d : Level = %3d  ", iOut, Gia_ObjLevel(p, pPivot) );
        if ( status == l_Undef )
            printf( "Timeout reached after %d seconds. ", nTimeOut );
        else if ( status == l_True )
            printf( "There is no false path. " );
        else
        {
            printf( "False path contains %d nodes (out of %d):  ", nLits, Vec_IntSize(vLits) );
            printf( "top = %d  ", Vec_IntEntry(vPath, Abc_Lit2Var(pLits[0])) );
            if ( fVeryVerbose )
                for ( i = 0; i < nLits; i++ )
                    printf( "%d ", Abc_Lit2Var(pLits[i]) );
            printf( "  " );
        }
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    }
    sat_solver_delete( pSat );
    Vec_IntFree( vObjs );
    Vec_IntFree( vPath );
    Vec_IntFree( vLits );
}
Gia_Man_t * Gia_ManCheckFalse( Gia_Man_t * p, int nSlackMax, int nTimeOut, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * pNew;
    Vec_Wec_t * vHooks;
    Vec_Que_t * vPrio;
    Vec_Flt_t * vWeights;
    Gia_Obj_t * pObj;
    int i;
    srand( 111 );
    Gia_ManLevelNum( p );
    // create PO weights
    vWeights = Vec_FltAlloc( Gia_ManCoNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_FltPush( vWeights, Gia_ObjLevel(p, pObj) );
    // put POs into the queue
    vPrio = Vec_QueAlloc( Gia_ManCoNum(p) );
    Vec_QueSetPriority( vPrio, Vec_FltArrayP(vWeights) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_QuePush( vPrio, i );
    // work on each PO in the queue
    vHooks = Vec_WecStart( Gia_ManObjNum(p) );
    while ( Vec_QueTopPriority(vPrio) >= p->nLevels - nSlackMax )
        Gia_ManCheckFalseOne( p, Vec_QuePop(vPrio), nTimeOut, vHooks, fVerbose, fVeryVerbose );
    if ( fVerbose )
    printf( "Collected %d non-overlapping false paths.\n", Vec_WecSizeUsed(vHooks) );
    // reconstruct the AIG
    pNew = Gia_ManFalseRebuild( p, vHooks, fVerbose, fVeryVerbose );
    // cleanup
    Vec_WecFree( vHooks );
    Vec_FltFree( vWeights );
    Vec_QueFree( vPrio );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

