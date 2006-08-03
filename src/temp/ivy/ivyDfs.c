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

/**Function*************************************************************

  Synopsis    [Recursively detects combinational loops.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManIsAcyclic_rec( Ivy_Man_t * p, Ivy_Obj_t * pNode )
{
    if ( Ivy_ObjIsCi(pNode) || Ivy_ObjIsConst1(pNode) )
        return 1;
    assert( Ivy_ObjIsNode( pNode ) );
    // make sure the node is not visited
    assert( !Ivy_ObjIsTravIdPrevious(p, pNode) );
    // check if the node is part of the combinational loop
    if ( Ivy_ObjIsTravIdCurrent(p, pNode) )
    {
        fprintf( stdout, "Manager contains combinational loop!\n" );
        fprintf( stdout, "Node \"%d\" is encountered twice on the following path:\n",  Ivy_ObjId(pNode) );
        fprintf( stdout, " %d",  Ivy_ObjId(pNode) );
        return 0;
    }
    // mark this node as a node on the current path
    Ivy_ObjSetTravIdCurrent( p, pNode );
    // check if the fanin is visited
    if ( !Ivy_ObjIsTravIdPrevious(p, Ivy_ObjFanin0(pNode)) ) 
    {
        // traverse the fanin's cone searching for the loop
        if ( !Ivy_ManIsAcyclic_rec(p, Ivy_ObjFanin0(pNode)) )
        {
            // return as soon as the loop is detected
            fprintf( stdout, " <-- %d", Ivy_ObjId(Ivy_ObjFanin0(pNode)) );
            return 0;
        }
    }
    // check if the fanin is visited
    if ( !Ivy_ObjIsTravIdPrevious(p, Ivy_ObjFanin1(pNode)) ) 
    {
        // traverse the fanin's cone searching for the loop
        if ( !Ivy_ManIsAcyclic_rec(p, Ivy_ObjFanin1(pNode)) )
        {
            // return as soon as the loop is detected
            fprintf( stdout, " <-- %d", Ivy_ObjId(Ivy_ObjFanin1(pNode)) );
            return 0;
        }
    }
    // mark this node as a visited node
    Ivy_ObjSetTravIdPrevious( p, pNode );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Detects combinational loops.]

  Description [This procedure is based on the idea suggested by Donald Chai. 
  As we traverse the network and visit the nodes, we need to distinquish 
  three types of nodes: (1) those that are visited for the first time, 
  (2) those that have been visited in this traversal but are currently not 
  on the traversal path, (3) those that have been visited and are currently 
  on the travesal path. When the node of type (3) is encountered, it means 
  that there is a combinational loop. To mark the three types of nodes, 
  two new values of the traversal IDs are used.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManIsAcyclic( Ivy_Man_t * p )
{
    Ivy_Obj_t * pNode;
    int fAcyclic, i;
    // set the traversal ID for this DFS ordering
    Ivy_ManIncrementTravId( p );   
    Ivy_ManIncrementTravId( p );   
    // pNode->TravId == pNet->nTravIds      means "pNode is on the path"
    // pNode->TravId == pNet->nTravIds - 1  means "pNode is visited but is not on the path"
    // pNode->TravId <  pNet->nTravIds - 1  means "pNode is not visited"
    // traverse the network to detect cycles
    fAcyclic = 1;
    Ivy_ManForEachCo( p, pNode, i )
    {
        if ( Ivy_ObjIsTravIdPrevious(p, Ivy_ObjFanin0(pNode)) )
            continue;
        // traverse the output logic cone
        if ( fAcyclic = Ivy_ManIsAcyclic_rec(p, Ivy_ObjFanin0(pNode)) )
            continue;
        // stop as soon as the first loop is detected
        fprintf( stdout, " (cone of CO \"%d\")\n", Ivy_ObjFaninId0(pNode) );
        break;
    }
    return fAcyclic;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


