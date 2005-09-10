/**CFile****************************************************************

  FileName    [cutNode.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Procedures to compute cuts for a node.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutNode.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the pointer to the linked list of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_NodeReadCuts( Cut_Man_t * p, int Node )
{
    if ( Node >= p->vCuts->nSize )
        return NULL;
    return Vec_PtrEntry( p->vCuts, Node );
}

/**Function*************************************************************

  Synopsis    [Returns the pointer to the linked list of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeWriteCuts( Cut_Man_t * p, int Node, Cut_Cut_t * pList )
{
    Vec_PtrWriteEntry( p->vCuts, Node, pList );
}

/**Function*************************************************************

  Synopsis    [Sets the trivial cut for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeSetTriv( Cut_Man_t * p, int Node )
{
    assert( Cut_NodeReadCuts(p, Node) == NULL );
    Cut_NodeWriteCuts( p, Node, Cut_CutCreateTriv(p, Node) );
}

/**Function*************************************************************

  Synopsis    [Consider dropping cuts if they are useless by now.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeTryDroppingCuts( Cut_Man_t * p, int Node )
{
    int nFanouts;
    assert( p->vFanCounts );
    nFanouts = Vec_IntEntry( p->vFanCounts, Node );
    assert( nFanouts > 0 );
    if ( --nFanouts == 0 )
        Cut_NodeFreeCuts( p, Node );
    Vec_IntWriteEntry( p->vFanCounts, Node, nFanouts );
}

/**Function*************************************************************

  Synopsis    [Deallocates the cuts at the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeFreeCuts( Cut_Man_t * p, int Node )
{
    Cut_Cut_t * pList, * pCut, * pCut2;
    pList = Cut_NodeReadCuts( p, Node );
    if ( pList == NULL )
        return;
    Cut_ListForEachCutSafe( pList, pCut, pCut2 )
        Cut_CutRecycle( p, pCut );
    Cut_NodeWriteCuts( p, Node, NULL );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


