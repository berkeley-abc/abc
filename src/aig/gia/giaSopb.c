/**CFile****************************************************************

  FileName    [giaSopb.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SOP balancing for a window.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSopb.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

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
void Gia_ManHighlight_rec( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsAnd(pObj) )
        Gia_ManHighlight_rec( p, Gia_ObjFaninId0(pObj, iObj) );
    if ( Gia_ObjIsAnd(pObj) )
        Gia_ManHighlight_rec( p, Gia_ObjFaninId1(pObj, iObj) );
}
void Gia_ManPrepareWin( Gia_Man_t * p, Vec_Int_t * vOuts, Vec_Int_t ** pvPis, Vec_Int_t ** pvPos, Vec_Int_t ** pvAnds )
{
    Gia_Obj_t * pObj;
    int i;
    // mark the section
    Gia_ManIncrementTravId( p );
    Gia_ManForEachCoVec( vOuts, p, pObj, i )
        Gia_ManHighlight_rec( p, Gia_ObjFaninId0p(p, pObj) );
    // mark fanins of the outside area
    Gia_ManCleanMark0( p );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            continue;
        if ( Gia_ObjIsAnd(pObj) && !Gia_ObjIsTravIdCurrentId(p, i) )
            continue;
        Gia_ObjFanin0(pObj)->fMark0 = 1;
        if ( Gia_ObjIsAnd(pObj) )
            Gia_ObjFanin1(pObj)->fMark0 = 1;
    }
    // collect pointed nodes
    *pvPis  = Vec_IntAlloc( 1000 );
    *pvPos  = Vec_IntAlloc( 1000 );
    *pvAnds = Vec_IntAlloc( 1000 );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( !Gia_ObjIsTravIdCurrentId(p, i) )
            continue;
        if ( Gia_ObjIsCi(pObj) )
            Vec_IntPush( *pvPis, i );
        else if ( pObj->fMark0 )
            Vec_IntPush( *pvPos, i );
        if ( Gia_ObjIsAnd(pObj) )
            Vec_IntPush( *pvAnds, i );
    }
    Gia_ManCleanMark0( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManExtractWin( Gia_Man_t * p, Vec_Int_t * vOuts )
{
    Vec_Int_t * vPis, * vPos, * vAnds;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManPrepareWin( p, vOuts, &vPis, &vPos, &vAnds );
    // create AIG
    pNew = Gia_ManStart( Vec_IntSize(vPis) + Vec_IntSize(vPos) + Vec_IntSize(vAnds) + 1 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObjVec( vPis, p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachObjVec( vPos, p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    Vec_IntFree( vPis );
    Vec_IntFree( vPos );
    Vec_IntFree( vAnds );
    return pNew;
}
Gia_Man_t * Gia_ManInsertWin( Gia_Man_t * p, Vec_Int_t * vOuts, Gia_Man_t * pWin )
{
    Vec_Int_t * vPos, * vPis, * vAnds;
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManPrepareWin( p, vOuts, &vPis, &vPos, &vAnds );
    // create AIG
    pNew = Gia_ManStart( Gia_ManObjNum(p) - Vec_IntSize(vAnds) + Gia_ManAndNum(pWin) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // inputs
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManConst0(pWin)->Value = 0;
    Gia_ManForEachCi( pWin, pObj, i )
        pObj->Value = Gia_ManObj(p, Vec_IntEntry(vPis, i))->Value;
    // internal nodes
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachAnd( pWin, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pWin, pObj, i )
        Gia_ManObj( p, Vec_IntEntry(vPos, i) )->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachAnd( p, pObj, i )
        if ( !Gia_ObjIsTravIdCurrentId(p, i) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    // cleanup
    Vec_IntFree( vPis );
    Vec_IntFree( vPos );
    Vec_IntFree( vAnds );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManFindLatest( Gia_Man_t * p, int LevelMax )
{
    Vec_Int_t * vOuts;
    Gia_Obj_t * pObj;
    int i;
    vOuts = Vec_IntAlloc( 1000 );
    Gia_ManForEachCo( p, pObj, i )
        if ( Gia_ObjLevel(p, pObj) > LevelMax )
            Vec_IntPush( vOuts, i );
    return vOuts;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManPerformSopBalanceWin( Gia_Man_t * p, int LevelMax, int nLevelRatio, int nCutNum, int nRelaxRatio, int fVerbose )
{
    Vec_Int_t * vOuts;
    Gia_Man_t * pNew, * pWin, * pWinNew;
    int nLevels = Gia_ManLevelNum( p );
    if ( nLevelRatio )
        LevelMax = (int)((1.0 - 0.01 * nLevelRatio) * nLevels);
//printf( "Using LevelMax = %d.\n", LevelMax );
    vOuts = Gia_ManFindLatest( p, LevelMax );
    if ( Vec_IntSize(vOuts) == 0 )
    {
        Vec_IntFree( vOuts );
        return Gia_ManDup( p );
    }
    pWin = Gia_ManExtractWin( p, vOuts );
    pWinNew = Gia_ManPerformSopBalance( pWin, nCutNum, nRelaxRatio, fVerbose );
    Gia_ManStop( pWin );
    pNew = Gia_ManInsertWin( p, vOuts, pWinNew );
    Gia_ManStop( pWinNew );
    Vec_IntFree( vOuts );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

