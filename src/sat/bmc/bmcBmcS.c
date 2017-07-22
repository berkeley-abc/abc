/**CFile****************************************************************

  FileName    [bmcBmcS.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [New BMC package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 20, 2017.]

  Revision    [$Id: bmcBmcS.c,v 1.00 2017/07/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "bmc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Incremental unfolding.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_SuperBuildTents_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vIns, Vec_Int_t * vCuts, Vec_Int_t * vFlops, Vec_Int_t * vObjs, Vec_Int_t * vRankIns, Vec_Int_t * vRankCuts, int Rank )
{
    Gia_Obj_t * pObj;
    if ( iObj == 0 )
        return;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    pObj = Gia_ManObj( p, iObj );
    if ( pObj->fMark0 )
    {
        if ( !pObj->fMark1 )
            return;
        Vec_IntPush( vCuts, iObj );
        Vec_IntPush( vRankCuts, Rank );
        pObj->fMark1 = 1;
        return;
    }
    pObj->fMark0 = 1;
    if ( Gia_ObjIsPi(p, pObj) )
    {
        Vec_IntPush( vIns, iObj );
        Vec_IntPush( vRankIns, Rank );
        pObj->fMark1 = 1;
        return;
    }
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vFlops, iObj );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Bmc_SuperBuildTents_rec( p, Gia_ObjFaninId0(pObj, iObj), vIns, vCuts, vFlops, vObjs, vRankIns, vRankCuts, Rank );
    Bmc_SuperBuildTents_rec( p, Gia_ObjFaninId1(pObj, iObj), vIns, vCuts, vFlops, vObjs, vRankIns, vRankCuts, Rank );
    Vec_IntPush( vObjs, iObj );
}
Gia_Man_t * Bmc_SuperBuildTents( Gia_Man_t * p, Vec_Int_t ** pvMap )
{
    Vec_Int_t * vIns      = Vec_IntAlloc( 1000 );
    Vec_Int_t * vCuts     = Vec_IntAlloc( 1000 );
    Vec_Int_t * vFlops    = Vec_IntAlloc( 1000 );
    Vec_Int_t * vObjs     = Vec_IntAlloc( 1000 );
    Vec_Int_t * vLimIns   = Vec_IntAlloc( 1000 );
    Vec_Int_t * vLimCuts  = Vec_IntAlloc( 1000 );
    Vec_Int_t * vLimFlops = Vec_IntAlloc( 1000 );
    Vec_Int_t * vLimObjs  = Vec_IntAlloc( 1000 );
    Vec_Int_t * vRankIns  = Vec_IntAlloc( 1000 );
    Vec_Int_t * vRankCuts = Vec_IntAlloc( 1000 );
    Vec_Int_t * vMap      = Vec_IntAlloc( 1000 );
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, r, Entry, Rank, iPrev, iThis = 0;
    // collect internal nodes
    Gia_ManForEachPo( p, pObj, i )
        Vec_IntPush( vFlops, Gia_ObjId(p, pObj) );
    Gia_ManCleanMark01( p );
    for ( Rank = 0; iThis < Vec_IntEntryLast(vFlops); Rank++ )
    {
        Vec_IntPush( vLimIns,   Vec_IntSize(vIns)   );
        Vec_IntPush( vLimCuts,  Vec_IntSize(vCuts)  );
        Vec_IntPush( vLimFlops, Vec_IntSize(vFlops) );
        Vec_IntPush( vLimObjs,  Vec_IntSize(vObjs)  );
        iPrev = iThis;
        iThis = Vec_IntEntryLast(vFlops);
        Vec_IntForEachEntryStartStop( vFlops, Entry, i, iPrev, iThis )
        {
            Gia_ManIncrementTravId( p );
            Bmc_SuperBuildTents_rec( p, Gia_ObjFaninId0(Gia_ManObj(p, iPrev), iPrev), vIns, vCuts, vFlops, vObjs, vRankIns, vRankCuts, Rank );
        }
    }
    Gia_ManCleanMark01( p );
    Vec_IntPush( vLimIns,   Vec_IntSize(vIns)   );
    Vec_IntPush( vLimCuts,  Vec_IntSize(vCuts)  );
    Vec_IntPush( vLimFlops, Vec_IntSize(vFlops) );
    Vec_IntPush( vLimObjs,  Vec_IntSize(vObjs)  );
    // create new GIA
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObjVec( vIns, p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachObjVec( vCuts, p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    for ( r = Rank; r >= 0; r-- )
    {
        Vec_IntForEachEntryStartStop( vFlops, Entry, i, Vec_IntEntry(vLimFlops, r), Vec_IntEntry(vLimFlops, r+1) )
        {
            pObj = Gia_ManObj(p, Entry);
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        }
        Vec_IntForEachEntryStartStop( vObjs, Entry, i, Vec_IntEntry(vLimObjs, r), Vec_IntEntry(vLimObjs, r+1) )
        {
            pObj = Gia_ManObj(p, Entry);
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        }
    }
    Gia_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachObjVec( vCuts, p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Vec_IntSize(vCuts) );

    // create map
    Vec_IntForEachEntryTwo( vIns, vRankIns, Entry, Rank, i )
        Vec_IntPushTwo( vMap, Entry, Rank );
    Vec_IntForEachEntryTwo( vCuts, vRankCuts, Entry, Rank, i )
        Vec_IntPushTwo( vMap, Entry, Rank );

    Vec_IntFree( vIns   );
    Vec_IntFree( vCuts  );
    Vec_IntFree( vFlops );
    Vec_IntFree( vObjs  );

    Vec_IntFree( vLimIns   );
    Vec_IntFree( vLimCuts  );
    Vec_IntFree( vLimFlops );
    Vec_IntFree( vLimObjs  );

    Vec_IntFree( vRankIns  );
    Vec_IntFree( vRankCuts  );

    if ( pvMap )
        *pvMap = vMap;
    else
        Vec_IntFree( vMap );

    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

