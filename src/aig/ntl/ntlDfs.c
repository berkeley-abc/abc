/**CFile****************************************************************

  FileName    [ntlDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [DFS traversal.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManDfs_rec( Ntl_Man_t * p, Ntl_Net_t * pNet )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNetFanin;
    int i;
    // skip visited
    if ( pNet->nVisits == 2 ) 
        return 1;
    // if the node is on the path, this is a combinational loop
    if ( pNet->nVisits == 1 )
        return 0; 
    // mark the node as the one on the path
    pNet->nVisits = 1;
    // derive the box
    pObj = pNet->pDriver;
    assert( Ntl_ObjIsNode(pObj) || Ntl_ObjIsBox(pObj) );
    // visit the input nets of the box
    Ntl_ObjForEachFanin( pObj, pNetFanin, i )
        if ( !Ntl_ManDfs_rec( p, pNetFanin ) )
            return 0;
    // add box inputs/outputs to COs/CIs
    if ( Ntl_ObjIsBox(pObj) )
    {
        Ntl_ObjForEachFanin( pObj, pNetFanin, i )
            Vec_PtrPush( p->vCos, pNetFanin );
        Ntl_ObjForEachFanout( pObj, pNetFanin, i )
            Vec_PtrPush( p->vCis, pNetFanin );
    }
    // store the node
    Vec_PtrPush( p->vNodes, pObj );
    pNet->nVisits = 2;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs DFS.]

  Description [Checks for combinational loops. Collects PI/PO nets.
  Collects nodes in the topological order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManDfs( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, nUselessObjects;
    assert( Vec_PtrSize(p->vCis) == 0 );
    assert( Vec_PtrSize(p->vCos) == 0 );
    assert( Vec_PtrSize(p->vNodes) == 0 );
    // get the root model
    pRoot = Vec_PtrEntry( p->vModels, 0 );
    // collect primary inputs
    Ntl_ModelForEachPi( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        Vec_PtrPush( p->vCis, pNet );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManDfs(): Primary input appears twice in the list.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // collect latch outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        Vec_PtrPush( p->vCis, pNet );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManDfs(): Latch output is duplicated or defined as a primary input.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // visit the nodes starting from primary outputs
    Ntl_ModelForEachPo( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManDfs_rec( p, pNet ) )
        {
            printf( "Ntl_ManDfs(): Error: Combinational loop is detected.\n" );
            Vec_PtrClear( p->vCis );
            Vec_PtrClear( p->vCos );
            Vec_PtrClear( p->vNodes );
            return 0;
        }
        Vec_PtrPush( p->vCos, pNet );
    }
    // visit the nodes starting from latch inputs outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManDfs_rec( p, pNet ) )
        {
            printf( "Ntl_ManDfs(): Error: Combinational loop is detected.\n" );
            Vec_PtrClear( p->vCis );
            Vec_PtrClear( p->vCos );
            Vec_PtrClear( p->vNodes );
            return 0;
        }
        Vec_PtrPush( p->vCos, pNet );
    }
    // report the number of dangling objects
    nUselessObjects = Ntl_ModelNodeNum(pRoot) + Ntl_ModelBoxNum(pRoot) - Vec_PtrSize(p->vNodes);
    if ( nUselessObjects )
        printf( "The number of nodes that do not feed into POs = %d.\n", nUselessObjects );
    return 1;    
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


