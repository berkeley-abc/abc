/**CFile****************************************************************

  FileName    [aigCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigCheck.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Makes sure that every node in the table is in the network and vice versa.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Aig_ManCheck( Aig_Man_t * pMan )
{
    Aig_Node_t * pObj, * pAnd;
    int i;
    Aig_ManForEachNode( pMan, pObj, i )
    {
        if ( pObj == pMan->pConst1 || Aig_NodeIsPi(pObj) )
        {
            if ( pObj->Fans[0].iNode || pObj->Fans[1].iNode || pObj->Level )
            {
                printf( "Aig_ManCheck: The AIG has non-standard constant or PI node \"%d\".\n", pObj->Id );
                return 0;
            }
            continue;
        }
        if ( Aig_NodeIsPo(pObj) )
        {
            if ( pObj->Fans[1].iNode )
            {
                printf( "Aig_ManCheck: The AIG has non-standard PO node \"%d\".\n", pObj->Id );
                return 0;
            }
            continue;
        }
        // consider the AND node
        if ( !pObj->Fans[0].iNode || !pObj->Fans[1].iNode )
        {
            printf( "Aig_ManCheck: The AIG has node \"%d\" with a constant fanin.\n", pObj->Id );
            return 0;
        }
        if ( pObj->Fans[0].iNode > pObj->Fans[1].iNode )
        {
            printf( "Aig_ManCheck: The AIG has node \"%d\" with a wrong ordering of fanins.\n", pObj->Id );
            return 0;
        }
        if ( pObj->Level != 1 + AIG_MAX(Aig_NodeFanin0(pObj)->Level, Aig_NodeFanin1(pObj)->Level) )
            printf( "Aig_ManCheck: Node \"%d\" has level that does not agree with the fanin levels.\n", pObj->Id );
        pAnd = Aig_TableLookupNode( pMan, Aig_NodeChild0(pObj), Aig_NodeChild1(pObj) );
        if ( pAnd != pObj )
            printf( "Aig_ManCheck: Node \"%d\" is not in the structural hashing table.\n", pObj->Id );
    }
    // count the number of nodes in the table
    if ( Aig_TableNumNodes(pMan->pTable) != Aig_ManAndNum(pMan) )
    {
        printf( "Aig_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Check if the node has a combination loop of depth 1 or 2.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Aig_NodeIsAcyclic( Aig_Node_t * pNode, Aig_Node_t * pRoot )
{
    Aig_Node_t * pFanin0, * pFanin1;
    Aig_Node_t * pChild00, * pChild01;
    Aig_Node_t * pChild10, * pChild11;
    if ( !Aig_NodeIsAnd(pNode) )
        return 1;
    pFanin0 = Aig_NodeFanin0(pNode);
    pFanin1 = Aig_NodeFanin1(pNode);
    if ( pRoot == pFanin0 || pRoot == pFanin1 )
        return 0;
    if ( Aig_NodeIsPi(pFanin0) )
    {
        pChild00 = NULL;
        pChild01 = NULL;
    }
    else
    {
        pChild00 = Aig_NodeFanin0(pFanin0);
        pChild01 = Aig_NodeFanin1(pFanin0);
        if ( pRoot == pChild00 || pRoot == pChild01 )
            return 0;
    }
    if ( Aig_NodeIsPi(pFanin1) )
    {
        pChild10 = NULL;
        pChild11 = NULL;
    }
    else
    {
        pChild10 = Aig_NodeFanin0(pFanin1);
        pChild11 = Aig_NodeFanin1(pFanin1);
        if ( pRoot == pChild10 || pRoot == pChild11 )
            return 0;
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


