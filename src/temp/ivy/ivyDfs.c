/**CFile****************************************************************

  FileName    [ivyDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [DFS collection procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyDfs.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManDfs_rec( Ivy_Obj_t * pObj, Vec_Int_t * vNodes )
{
    if ( Ivy_ObjIsConst1(pObj) || Ivy_ObjIsCi(pObj) )
        return;
    if ( Ivy_ObjIsMarkA(pObj) )
        return;
    Ivy_ObjSetMarkA(pObj);
    assert( Ivy_ObjIsBuf(pObj) || Ivy_ObjIsAnd(pObj) || Ivy_ObjIsExor(pObj) );
    Ivy_ManDfs_rec( Ivy_ObjFanin0(pObj), vNodes );
    if ( !Ivy_ObjIsBuf(pObj) )
        Ivy_ManDfs_rec( Ivy_ObjFanin1(pObj), vNodes );
    Vec_IntPush( vNodes, pObj->Id );
}

/**Function*************************************************************

  Synopsis    [Collects AND/EXOR nodes in the DFS order from CIs to COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_ManDfs( Ivy_Man_t * p )
{
    Vec_Int_t * vNodes;
    Ivy_Obj_t * pObj;
    int i;
    assert( Ivy_ManLatchNum(p) == 0 );
    // make sure the nodes are not marked
    Ivy_ManForEachObj( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    // collect the nodes
    vNodes = Vec_IntAlloc( Ivy_ManNodeNum(p) );
    Ivy_ManForEachPo( p, pObj, i )
        Ivy_ManDfs_rec( Ivy_ObjFanin0(pObj), vNodes );
    // unmark the collected nodes
    Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
        Ivy_ObjClearMarkA(pObj);
    // make sure network does not have dangling nodes
    assert( Vec_IntSize(vNodes) == Ivy_ManNodeNum(p) + Ivy_ManBufNum(p) );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects AND/EXOR nodes in the DFS order from CIs to COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_ManDfsSeq( Ivy_Man_t * p, Vec_Int_t ** pvLatches )
{
    Vec_Int_t * vNodes, * vLatches;
    Ivy_Obj_t * pObj;
    int i;
    assert( Ivy_ManLatchNum(p) > 0 );
    // make sure the nodes are not marked
    Ivy_ManForEachObj( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    // collect the latches
    vLatches = Vec_IntAlloc( Ivy_ManLatchNum(p) );
    Ivy_ManForEachLatch( p, pObj, i )
        Vec_IntPush( vLatches, pObj->Id );
    // collect the nodes
    vNodes = Vec_IntAlloc( Ivy_ManNodeNum(p) );
    Ivy_ManForEachPo( p, pObj, i )
        Ivy_ManDfs_rec( Ivy_ObjFanin0(pObj), vNodes );
    Ivy_ManForEachNodeVec( p, vLatches, pObj, i )
        Ivy_ManDfs_rec( Ivy_ObjFanin0(pObj), vNodes );
    // unmark the collected nodes
    Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
        Ivy_ObjClearMarkA(pObj);
    // make sure network does not have dangling nodes
    assert( Vec_IntSize(vNodes) == Ivy_ManNodeNum(p) + Ivy_ManBufNum(p) );
    *pvLatches = vLatches;
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCollectCone_rec( Ivy_Obj_t * pObj, Vec_Ptr_t * vCone )
{
    if ( pObj->fMarkA )
        return;
    if ( Ivy_ObjIsBuf(pObj) )
    {
        Ivy_ManCollectCone_rec( Ivy_ObjFanin0(pObj), vCone );
        Vec_PtrPush( vCone, pObj );
        return;
    }
    assert( Ivy_ObjIsNode(pObj) );
    Ivy_ManCollectCone_rec( Ivy_ObjFanin0(pObj), vCone );
    Ivy_ManCollectCone_rec( Ivy_ObjFanin1(pObj), vCone );
    Vec_PtrPushUnique( vCone, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCollectCone( Ivy_Obj_t * pObj, Vec_Ptr_t * vFront, Vec_Ptr_t * vCone )
{
    Ivy_Obj_t * pTemp;
    int i;
    assert( !Ivy_IsComplement(pObj) );
    assert( Ivy_ObjIsNode(pObj) );
    // mark the nodes
    Vec_PtrForEachEntry( vFront, pTemp, i )
        Ivy_Regular(pTemp)->fMarkA = 1;
    assert( pObj->fMarkA == 0 );
    // collect the cone
    Vec_PtrClear( vCone );
    Ivy_ManCollectCone_rec( pObj, vCone );
    // unmark the nodes
    Vec_PtrForEachEntry( vFront, pTemp, i )
        Ivy_Regular(pTemp)->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Returns the nodes by level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Ivy_ManLevelize( Ivy_Man_t * p )
{
    Vec_Vec_t * vNodes;
    Ivy_Obj_t * pObj;
    int i;
    vNodes = Vec_VecAlloc( 100 );
    Ivy_ManForEachObj( p, pObj, i )
    {
        assert( !Ivy_ObjIsBuf(pObj) );
        if ( Ivy_ObjIsNode(pObj) )
            Vec_VecPush( vNodes, pObj->Level, pObj );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Computes required levels for each node.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_ManRequiredLevels( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj;
    Vec_Int_t * vLevelsR;
    Vec_Vec_t * vNodes;
    int i, k, Level, LevelMax;
    assert( p->vRequired == NULL );
    // start the required times
    vLevelsR = Vec_IntStart( Ivy_ManObjIdMax(p) + 1 );
    // iterate through the nodes in the reverse order
    vNodes = Ivy_ManLevelize( p );
    Vec_VecForEachEntryReverseReverse( vNodes, pObj, i, k )
    {
        Level = Vec_IntEntry( vLevelsR, pObj->Id ) + 1 + Ivy_ObjIsExor(pObj);
        if ( Vec_IntEntry( vLevelsR, Ivy_ObjFaninId0(pObj) ) < Level )
            Vec_IntWriteEntry( vLevelsR, Ivy_ObjFaninId0(pObj), Level );
        if ( Vec_IntEntry( vLevelsR, Ivy_ObjFaninId1(pObj) ) < Level )
            Vec_IntWriteEntry( vLevelsR, Ivy_ObjFaninId1(pObj), Level );
    }
    Vec_VecFree( vNodes );
    // convert it into the required times
    LevelMax = Ivy_ManLevels( p );
//printf( "max %5d\n",LevelMax );
    Ivy_ManForEachObj( p, pObj, i )
    {
        Level = Vec_IntEntry( vLevelsR, pObj->Id );
        Vec_IntWriteEntry( vLevelsR, pObj->Id, LevelMax - Level );
//printf( "%5d : %5d %5d\n", pObj->Id, Level, LevelMax - Level );
    }
    p->vRequired = vLevelsR;
    return vLevelsR;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


