/**CFile****************************************************************

  FileName    [aigUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManIncrementTravId( Aig_Man_t * pMan )
{
    Aig_Node_t * pObj;
    int i;
    if ( pMan->nTravIds == (1<<24)-1 )
    {
        pMan->nTravIds = 0;
        Aig_ManForEachNode( pMan, pObj, i )
            pObj->TravId = 0;
    }
    pMan->nTravIds++;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Aig_NodeIsMuxType( Aig_Node_t * pNode )
{
    Aig_Node_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Aig_IsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Aig_NodeIsAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Aig_NodeFaninC0(pNode) || !Aig_NodeFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Aig_NodeFanin0(pNode);
    pNode1 = Aig_NodeFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( !Aig_NodeIsAnd(pNode0) || !Aig_NodeIsAnd(pNode1) )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Aig_NodeFaninId0(pNode0) == Aig_NodeFaninId0(pNode1) && (Aig_NodeFaninC0(pNode0) ^ Aig_NodeFaninC0(pNode1))) || 
           (Aig_NodeFaninId0(pNode0) == Aig_NodeFaninId1(pNode1) && (Aig_NodeFaninC0(pNode0) ^ Aig_NodeFaninC1(pNode1))) ||
           (Aig_NodeFaninId1(pNode0) == Aig_NodeFaninId0(pNode1) && (Aig_NodeFaninC1(pNode0) ^ Aig_NodeFaninC0(pNode1))) ||
           (Aig_NodeFaninId1(pNode0) == Aig_NodeFaninId1(pNode1) && (Aig_NodeFaninC1(pNode0) ^ Aig_NodeFaninC1(pNode1)));
}

/**Function*************************************************************

  Synopsis    [Recognizes what nodes are control and data inputs of a MUX.]

  Description [If the node is a MUX, returns the control variable C.
  Assigns nodes T and E to be the then and else variables of the MUX. 
  Node C is never complemented. Nodes T and E can be complemented.
  This function also recognizes EXOR/NEXOR gates as MUXes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_NodeRecognizeMux( Aig_Node_t * pNode, Aig_Node_t ** ppNodeT, Aig_Node_t ** ppNodeE )
{
    Aig_Node_t * pNode0, * pNode1;
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_NodeIsMuxType(pNode) );
    // get children
    pNode0 = Aig_NodeFanin0(pNode);
    pNode1 = Aig_NodeFanin1(pNode);
    // find the control variable
//    if ( pNode1->p1 == Fraig_Not(pNode2->p1) )
    if ( Aig_NodeFaninId0(pNode0) == Aig_NodeFaninId0(pNode1) && (Aig_NodeFaninC0(pNode0) ^ Aig_NodeFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Aig_NodeFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild1(pNode1));//pNode2->p2);
            *ppNodeE = Aig_Not(Aig_NodeChild1(pNode0));//pNode1->p2);
            return Aig_NodeChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild1(pNode0));//pNode1->p2);
            *ppNodeE = Aig_Not(Aig_NodeChild1(pNode1));//pNode2->p2);
            return Aig_NodeChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p1 == Fraig_Not(pNode2->p2) )
    else if ( Aig_NodeFaninId0(pNode0) == Aig_NodeFaninId1(pNode1) && (Aig_NodeFaninC0(pNode0) ^ Aig_NodeFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Aig_NodeFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild0(pNode1));//pNode2->p1);
            *ppNodeE = Aig_Not(Aig_NodeChild1(pNode0));//pNode1->p2);
            return Aig_NodeChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild1(pNode0));//pNode1->p2);
            *ppNodeE = Aig_Not(Aig_NodeChild0(pNode1));//pNode2->p1);
            return Aig_NodeChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p1) )
    else if ( Aig_NodeFaninId1(pNode0) == Aig_NodeFaninId0(pNode1) && (Aig_NodeFaninC1(pNode0) ^ Aig_NodeFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Aig_NodeFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild1(pNode1));//pNode2->p2);
            *ppNodeE = Aig_Not(Aig_NodeChild0(pNode0));//pNode1->p1);
            return Aig_NodeChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild0(pNode0));//pNode1->p1);
            *ppNodeE = Aig_Not(Aig_NodeChild1(pNode1));//pNode2->p2);
            return Aig_NodeChild1(pNode0);//pNode1->p2;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p2) )
    else if ( Aig_NodeFaninId1(pNode0) == Aig_NodeFaninId1(pNode1) && (Aig_NodeFaninC1(pNode0) ^ Aig_NodeFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Aig_NodeFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild0(pNode1));//pNode2->p1);
            *ppNodeE = Aig_Not(Aig_NodeChild0(pNode0));//pNode1->p1);
            return Aig_NodeChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_NodeChild0(pNode0));//pNode1->p1);
            *ppNodeE = Aig_Not(Aig_NodeChild0(pNode1));//pNode2->p1);
            return Aig_NodeChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


