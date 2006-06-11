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
    // collect the nodes
    vNodes = Vec_IntAlloc( Ivy_ManNodeNum(p) );
    if ( Ivy_ManLatchNum(p) > 0 )
        Ivy_ManForEachCo( p, pObj, i )
            Ivy_ManDfs_rec( Ivy_ObjFanin0(pObj), vNodes );
    else
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

  Synopsis    [Collects nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManDfsExt_rec( Ivy_Obj_t * pObj, Vec_Int_t * vNodes )
{
    Vec_Int_t * vFanins;
    int i, Fanin;
    if ( !Ivy_ObjIsNodeExt(pObj) || Ivy_ObjIsMarkA(pObj) )
        return;
    // mark the node as visited
    Ivy_ObjSetMarkA(pObj);
    // traverse the fanins
    vFanins = Ivy_ObjGetFanins( pObj );
    Vec_IntForEachEntry( vFanins, Fanin, i )
        Ivy_ManDfsExt_rec( Ivy_ObjObj(pObj, Ivy_FanId(Fanin)), vNodes );
    // add the node
    Vec_IntPush( vNodes, pObj->Id );
} 

/**Function*************************************************************

  Synopsis    [Collects nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_ManDfsExt( Ivy_Man_t * p )
{
    Vec_Int_t * vNodes;
    Ivy_Obj_t * pObj, * pFanin;
    int i;
    assert( p->fExtended ); 
    assert( Ivy_ManLatchNum(p) == 0 ); 
    // make sure network does not have buffers
    vNodes = Vec_IntAlloc( 10 );
    Ivy_ManForEachPo( p, pObj, i )
    {
        pFanin = Ivy_ManObj( p, Ivy_FanId( Ivy_ObjReadFanin(pObj,0) ) );
        Ivy_ManDfsExt_rec( pFanin, vNodes );
    }
    Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
        Ivy_ObjClearMarkA(pObj);
    // make sure network does not have dangling nodes
    // the network may have dangling nodes if some fanins of ESOPs do not appear in cubes
//    assert( p->nNodes == Vec_PtrSize(vNodes) );
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


