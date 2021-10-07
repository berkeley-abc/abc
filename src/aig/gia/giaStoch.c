/**CFile****************************************************************

  FileName    [giaDeep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experiments with synthesis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDeep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

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
static void Vec_PtrFreeFunc( Vec_Ptr_t * p, void (*pFuncItemFree)(void *) ) ___unused;
static void Vec_PtrFreeFunc( Vec_Ptr_t * p, void (*pFuncItemFree)(void *) )
{
    void * pItem; int i;
    Vec_PtrForEachEntry( void *, p, pItem, i )
        pFuncItemFree( pItem );
    Vec_PtrFree( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStochSynthesis( Vec_Ptr_t * vAigs, char * pScript )
{
    Gia_Man_t * pGia, * pNew; int i;
    Vec_PtrForEachEntry( Gia_Man_t *, vAigs, pGia, i )
    {
        Gia_Man_t * pCopy = Gia_ManDup(pGia);
        Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
        if ( Abc_FrameIsBatchMode() )
        {
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
                return;
            }
        }
        else
        {
            Abc_FrameSetBatchMode( 1 );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
                Abc_FrameSetBatchMode( 0 );
                return;
            }
            Abc_FrameSetBatchMode( 0 );
        }
        pNew = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
        if ( Gia_ManAndNum(pNew) < Gia_ManAndNum(pCopy) )
        {
            Gia_ManStop( pCopy );
            pCopy = Gia_ManDup( pNew );
        }
        Vec_PtrWriteEntry( vAigs, i, pCopy );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDivideOne( Gia_Man_t * p, Vec_Int_t * vCis, Vec_Int_t * vAnds, Vec_Int_t * vCos )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj; int i;
    pNew = Gia_ManStart( 1+Vec_IntSize(vCis)+Vec_IntSize(vAnds)+Vec_IntSize(vCos) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObjVec( vCis, p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachObjVec( vCos, p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    assert( Gia_ManCiNum(pNew) > 0 && Gia_ManCoNum(pNew) > 0 );
    return pNew;
}
Vec_Ptr_t * Gia_ManDupDivide( Gia_Man_t * p, Vec_Wec_t * vCis, Vec_Wec_t * vAnds, Vec_Wec_t * vCos, char * pScript )
{
    Vec_Ptr_t * vAigs = Vec_PtrAlloc( Vec_WecSize(vCis) );  int i;
    for ( i = 0; i < Vec_WecSize(vCis); i++ )
        Vec_PtrPush( vAigs, Gia_ManDupDivideOne(p, Vec_WecEntry(vCis, i), Vec_WecEntry(vAnds, i), Vec_WecEntry(vCos, i)) );
    Gia_ManStochSynthesis( vAigs, pScript );
    return vAigs;
}
Gia_Man_t * Gia_ManDupStitch( Gia_Man_t * p, Vec_Wec_t * vCis, Vec_Wec_t * vAnds, Vec_Wec_t * vCos, Vec_Ptr_t * vAigs )
{
    Gia_Man_t * pGia, * pNew;
    Gia_Obj_t * pObj; int i, k;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManCleanValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManHashAlloc( pNew );
    Vec_PtrForEachEntry( Gia_Man_t *, vAigs, pGia, i )
    {
        Vec_Int_t * vCi = Vec_WecEntry( vCis, i );
        Vec_Int_t * vCo = Vec_WecEntry( vCos, i );
        Gia_ManCleanValue( pGia );
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachObjVec( vCi, p, pObj, k )
            Gia_ManCi(pGia, k)->Value = pObj->Value;
        Gia_ManForEachAnd( pGia, pObj, k )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachObjVec( vCo, p, pObj, k )
            pObj->Value = Gia_ObjFanin0Copy(Gia_ManCo(pGia, k));
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    pNew = Gia_ManCleanup( pGia = pNew );
    Gia_ManStop( pGia );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStochCollect_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vAnds )
{
    Gia_Obj_t * pObj;
    if ( Gia_ObjUpdateTravIdCurrentId( p, iObj ) )
        return;
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsCi(pObj) || iObj == 0 )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManStochCollect_rec( p, Gia_ObjFaninId0(pObj, iObj), vAnds );
    Gia_ManStochCollect_rec( p, Gia_ObjFaninId1(pObj, iObj), vAnds );
    Vec_IntPush( vAnds, iObj );
}
Vec_Wec_t * Gia_ManStochNodes( Gia_Man_t * p, int nMaxSize, int Seed )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vPart = Vec_WecPushLevel( vRes );
    int i, iStart = Seed % Gia_ManCoNum(p);
    //Gia_ManLevelNum( p );
    Gia_ManIncrementTravId( p );
    for ( i = 0; i < Gia_ManCoNum(p); i++ )
    {
        Gia_Obj_t * pObj = Gia_ManCo( p, (iStart+i) % Gia_ManCoNum(p) );
        if ( Vec_IntSize(vPart) > nMaxSize )
            vPart = Vec_WecPushLevel( vRes );
        Gia_ManStochCollect_rec( p, Gia_ObjFaninId0p(p, pObj), vPart );
    }
    if ( Vec_IntSize(vPart) == 0 )
        Vec_WecShrink( vRes, Vec_WecSize(vRes)-1 );
    //Vec_WecPrint( vRes, 0 );
    return vRes;
}
Vec_Wec_t * Gia_ManStochInputs( Gia_Man_t * p, Vec_Wec_t * vAnds )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vLevel; Gia_Obj_t * pObj; int i, k, iObj;
    Vec_WecForEachLevel( vAnds, vLevel, i )
    {
        Vec_Int_t * vVec = Vec_WecPushLevel( vRes );
        Gia_ManIncrementTravId( p );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Gia_ObjSetTravIdCurrentId( p, iObj );
        Gia_ManForEachObjVec( vLevel, p, pObj, k )
        {
            iObj = Gia_ObjFaninId0p(p, pObj);
            if ( !Gia_ObjUpdateTravIdCurrentId(p, iObj) )
                Vec_IntPush( vVec, iObj );
            iObj = Gia_ObjFaninId1p(p, pObj);
            if ( !Gia_ObjUpdateTravIdCurrentId(p, iObj) )
                Vec_IntPush( vVec, iObj );
        }
    }
    return vRes;
}
Vec_Wec_t * Gia_ManStochOutputs( Gia_Man_t * p, Vec_Wec_t * vAnds )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vLevel; Gia_Obj_t * pObj; int i, k;
    Gia_ManCreateRefs( p );
    Vec_WecForEachLevel( vAnds, vLevel, i )
    {
        Vec_Int_t * vVec = Vec_WecPushLevel( vRes );
        Gia_ManForEachObjVec( vLevel, p, pObj, k )
        {
            Gia_ObjRefDecId( p, Gia_ObjFaninId0p(p, pObj) );
            Gia_ObjRefDecId( p, Gia_ObjFaninId1p(p, pObj) );
        }
        Gia_ManForEachObjVec( vLevel, p, pObj, k )
            if ( Gia_ObjRefNum(p, pObj) )
                Vec_IntPush( vVec, Gia_ObjId(p, pObj) );
        Gia_ManForEachObjVec( vLevel, p, pObj, k )
        {
            Gia_ObjRefIncId( p, Gia_ObjFaninId0p(p, pObj) );
            Gia_ObjRefIncId( p, Gia_ObjFaninId1p(p, pObj) );
        }
    }
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStochSyn( int nMaxSize, int nIters, int TimeOut, int Seed, int fVerbose, char * pScript )
{
    abctime nTimeToStop = TimeOut ? Abc_Clock() + TimeOut * CLOCKS_PER_SEC : 0;
    abctime clkStart    = Abc_Clock();
    int i, nEnd, nBeg   = Gia_ManAndNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    Abc_Random(1);
    for ( i = 0; i < 10+Seed; i++ )
        Abc_Random(0);
    if ( fVerbose )
    printf( "Running %d iterations of script \"%s\".\n", nIters, pScript );
    for ( i = 0; i < nIters; i++ )
    {
        abctime clk = Abc_Clock();
        Gia_Man_t * pGia  = Gia_ManDup( Abc_FrameReadGia(Abc_FrameGetGlobalFrame()) );
        Vec_Wec_t * vAnds = Gia_ManStochNodes( pGia, nMaxSize, Abc_Random(0) & 0x7FFFFFFF );
        Vec_Wec_t * vIns  = Gia_ManStochInputs( pGia, vAnds );
        Vec_Wec_t * vOuts = Gia_ManStochOutputs( pGia, vAnds );
        Vec_Ptr_t * vAigs = Gia_ManDupDivide( pGia, vIns, vAnds, vOuts, pScript );
        Gia_Man_t * pNew  = Gia_ManDupStitch( pGia, vIns, vAnds, vOuts, vAigs );
        Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pNew );
        if ( fVerbose )
        printf( "Iteration %3d : Using %3d partitions. Reducing %6d nodes to %6d nodes.  ", 
            i, Vec_PtrSize(vAigs), Gia_ManAndNum(pGia), Gia_ManAndNum(pNew) ); 
        if ( fVerbose )
        Abc_PrintTime( 0, "Time", Abc_Clock() - clk );
        Gia_ManStop( pGia );
        Vec_PtrFreeFunc( vAigs, (void (*)(void *)) Gia_ManStop );
        Vec_WecFree( vAnds );
        Vec_WecFree( vIns );
        Vec_WecFree( vOuts );
        if ( nTimeToStop && Abc_Clock() > nTimeToStop )
        {
            printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
            break;
        }
    }
    nEnd = Gia_ManAndNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    if ( fVerbose )
    printf( "Cumulatively reduced %d AIG nodes after %d iterations.  ", 
        nBeg - nEnd, nIters );
    if ( fVerbose )
    Abc_PrintTime( 0, "Total time", Abc_Clock() - clkStart );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

