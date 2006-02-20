/**CFile****************************************************************

  FileName    [aigNode.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigNode.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Node_t * Aig_NodeCreate( Aig_Man_t * p )
{
    Aig_Node_t * pNode;
    // create the node
    pNode = (Aig_Node_t *)Aig_MemFixedEntryFetch( p->mmNodes );
    memset( pNode, 0, sizeof(Aig_Node_t) );
    // assign the number and add to the array of nodes
    pNode->pMan = p;
    pNode->Id = p->vNodes->nSize;
    Vec_PtrPush( p->vNodes, pNode );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates the constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeCreateConst( Aig_Man_t * p )
{
    Aig_Node_t * pNode;
    pNode = Aig_NodeCreate( p );
    pNode->Type   = AIG_NONE;
    pNode->fPhase = 1; // sim value for 000... pattern
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates a primary input node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeCreatePi( Aig_Man_t * p )
{
    Aig_Node_t * pNode;
    pNode = Aig_NodeCreate( p );
    Vec_PtrPush( p->vPis, pNode );
    pNode->Type   = AIG_PI;
    pNode->fPhase =  0;  // sim value for 000... pattern
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates a primary output node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeCreatePo( Aig_Man_t * p )
{
    Aig_Node_t * pNode;
    pNode = Aig_NodeCreate( p );
    pNode->Type = AIG_PO;
    Vec_PtrPush( p->vPos, pNode );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates a primary output node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeConnectPo( Aig_Man_t * p, Aig_Node_t * pNode, Aig_Node_t * pFanin )
{
    assert( Aig_NodeIsPo(pNode) );
    assert( !Aig_IsComplement(pNode) );
    // connect to the fanin
    pNode->Fans[0].fComp = Aig_IsComplement(pFanin);
    pNode->Fans[0].iNode = Aig_Regular(pFanin)->Id;
    pNode->fPhase = pNode->Fans[0].fComp ^ Aig_Regular(pFanin)->fPhase;  // sim value for 000... pattern
    pNode->Level = Aig_Regular(pFanin)->Level;
    Aig_Regular(pFanin)->nRefs++;
    if ( pNode->pMan->vFanPivots )  Aig_NodeAddFaninFanout( pFanin, pNode );
    // update global level if needed
    if ( p->nLevelMax < (int)pNode->Level )
        p->nLevelMax = pNode->Level;
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates a new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeCreateAnd( Aig_Man_t * p, Aig_Node_t * pFanin0, Aig_Node_t * pFanin1 )
{
    Aig_Node_t * pNode;
    pNode = Aig_NodeCreate( p );
    pNode->Type = AIG_AND;
    Aig_NodeConnectAnd( pFanin0, pFanin1, pNode );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Connects the nodes to the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeConnectAnd( Aig_Node_t * pFanin0, Aig_Node_t * pFanin1, Aig_Node_t * pNode )
{
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_NodeIsAnd(pNode) );
    // add the fanins
    pNode->Fans[0].fComp = Aig_IsComplement(pFanin0);
    pNode->Fans[0].iNode = Aig_Regular(pFanin0)->Id;
    pNode->Fans[1].fComp = Aig_IsComplement(pFanin1);
    pNode->Fans[1].iNode = Aig_Regular(pFanin1)->Id;
    // compute the phase (sim value for 000... pattern)
    pNode->fPhase = (pNode->Fans[0].fComp ^ Aig_Regular(pFanin0)->fPhase) & 
                    (pNode->Fans[1].fComp ^ Aig_Regular(pFanin1)->fPhase);
    pNode->Level = Aig_NodeGetLevelNew(pNode);
    // reference the fanins
    Aig_Regular(pFanin0)->nRefs++;
    Aig_Regular(pFanin1)->nRefs++;
    // add the fanouts
    if ( pNode->pMan->vFanPivots )  Aig_NodeAddFaninFanout( pFanin0, pNode );
    if ( pNode->pMan->vFanPivots )  Aig_NodeAddFaninFanout( pFanin1, pNode );
    // add the node to the structural hash table
    Aig_TableInsertNode( pNode->pMan, pFanin0, pFanin1, pNode );
}

/**Function*************************************************************

  Synopsis    [Connects the nodes to the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeDisconnectAnd( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanin0, * pFanin1;
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_NodeIsAnd(pNode) );
    // get the fanins
    pFanin0 = Aig_NodeFanin0(pNode);
    pFanin1 = Aig_NodeFanin1(pNode);
    // dereference the fanins
    pFanin0->nRefs--;
    pFanin0->nRefs--;
    // remove the fanouts
    if ( pNode->pMan->vFanPivots )  Aig_NodeRemoveFaninFanout( pFanin0, pNode );
    if ( pNode->pMan->vFanPivots )  Aig_NodeRemoveFaninFanout( pFanin1, pNode );
    // remove the node from the structural hash table
    Aig_TableDeleteNode( pNode->pMan, pNode );
}

/**Function*************************************************************

  Synopsis    [Performs internal deletion step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeDeleteAnd_rec( Aig_Man_t * pMan, Aig_Node_t * pRoot )
{
    Aig_Node_t * pNode0, * pNode1;
    // make sure the node is regular and dangling
    assert( !Aig_IsComplement(pRoot) );
    assert( pRoot->nRefs == 0 );
    assert( Aig_NodeIsAnd(pRoot) );
    // remember the children
    pNode0 = Aig_NodeFanin0(pRoot);
    pNode1 = Aig_NodeFanin1(pRoot);
    // disconnect the node
    Aig_NodeDisconnectAnd( pRoot );
    // recycle the node
    Vec_PtrWriteEntry( pMan->vNodes, pRoot->Id, NULL );
    memset( pRoot, 0, sizeof(Aig_Node_t) ); // this is a temporary hack to skip dead children below!!!
    Aig_MemFixedEntryRecycle( pMan->mmNodes, (char *)pRoot );
    // call recursively
    if ( Aig_NodeIsAnd(pNode0) && pNode0->nRefs == 0 )
        Aig_NodeDeleteAnd_rec( pMan, pNode0 );
    if ( Aig_NodeIsAnd(pNode1) && pNode1->nRefs == 0 )
        Aig_NodeDeleteAnd_rec( pMan, pNode1 );
}

/**Function*************************************************************

  Synopsis    [Prints the AIG node for debugging purposes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodePrint( Aig_Node_t * pNode )
{
    Aig_Node_t * pNodeR = Aig_Regular(pNode);
    if ( Aig_NodeIsPi(pNode) )
    {
        printf( "PI %4s%s.\n", Aig_NodeName(pNode), Aig_IsComplement(pNode)? "\'" : "" );
        return;
    }
    if ( Aig_NodeIsConst(pNode) )
    {
        printf( "Constant 1 %s.\n", Aig_IsComplement(pNode)? "(complemented)" : ""  );
        return;
    }
    // print the node's function
    printf( "%7s%s", Aig_NodeName(pNodeR),                 Aig_IsComplement(pNode)? "\'" : "" );
    printf( " = " );
    printf( "%7s%s", Aig_NodeName(Aig_NodeFanin0(pNodeR)), Aig_NodeFaninC0(pNodeR)? "\'" : "" );
    printf( " * " );
    printf( "%7s%s", Aig_NodeName(Aig_NodeFanin1(pNodeR)), Aig_NodeFaninC1(pNodeR)? "\'" : "" );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Returns the name of the node.]

  Description [The name should be used before this procedure is called again.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Aig_NodeName( Aig_Node_t * pNode )
{
    static char Buffer[100];
    sprintf( Buffer, "%d", Aig_Regular(pNode)->Id );
    return Buffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


