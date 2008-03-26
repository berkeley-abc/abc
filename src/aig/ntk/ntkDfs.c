/**CFile****************************************************************

  FileName    [ntkDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [DFS traversals.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDfs_rec( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pNext;
    int i;
    if ( Ntk_ObjIsTravIdCurrent( pNode ) )
        return;
    Ntk_ObjSetTravIdCurrent( pNode );
    Ntk_ObjForEachFanin( pNode, pNext, i )
        Ntk_ManDfs_rec( pNext, vNodes );
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntk_ManDfs( Ntk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Ntk_Obj_t * pObj;
    int i;
    Ntk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Ntk_ManForEachPo( pNtk, pObj, i )
        Ntk_ManDfs_rec( pObj, vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDfsReverse_rec( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pNext;
    int i;
    if ( Ntk_ObjIsTravIdCurrent( pNode ) )
        return;
    Ntk_ObjSetTravIdCurrent( pNode );
    Ntk_ObjForEachFanout( pNode, pNext, i )
        Ntk_ManDfsReverse_rec( pNext, vNodes );
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntk_ManDfsReverse( Ntk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Ntk_Obj_t * pObj;
    int i;
    Ntk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Ntk_ManForEachPi( pNtk, pObj, i )
        Ntk_ManDfsReverse_rec( pObj, vNodes );
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


