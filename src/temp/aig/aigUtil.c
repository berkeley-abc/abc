/**CFile****************************************************************

  FileName    [aigUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Various procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aigUtil.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

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
void Aig_ManIncrementTravId( Aig_Man_t * p )
{
    if ( p->nTravIds >= (1<<30)-1 )
        Aig_ManCleanData( p );
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Sets the DFS ordering of the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCleanData( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    p->nTravIds = 1;
    Aig_ManConst1(p)->pData = NULL;
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = NULL;
    Aig_ManForEachPo( p, pObj, i )
        pObj->pData = NULL;
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ObjIsMuxType( Aig_Obj_t * pNode )
{
    Aig_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Aig_IsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Aig_ObjIsAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Aig_ObjFaninC0(pNode) || !Aig_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Aig_ObjFanin0(pNode);
    pNode1 = Aig_ObjFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( !Aig_ObjIsAnd(pNode0) || !Aig_ObjIsAnd(pNode1) )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Aig_ObjFanin0(pNode0) == Aig_ObjFanin0(pNode1) && (Aig_ObjFaninC0(pNode0) ^ Aig_ObjFaninC0(pNode1))) || 
           (Aig_ObjFanin0(pNode0) == Aig_ObjFanin1(pNode1) && (Aig_ObjFaninC0(pNode0) ^ Aig_ObjFaninC1(pNode1))) ||
           (Aig_ObjFanin1(pNode0) == Aig_ObjFanin0(pNode1) && (Aig_ObjFaninC1(pNode0) ^ Aig_ObjFaninC0(pNode1))) ||
           (Aig_ObjFanin1(pNode0) == Aig_ObjFanin1(pNode1) && (Aig_ObjFaninC1(pNode0) ^ Aig_ObjFaninC1(pNode1)));
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
Aig_Obj_t * Aig_ObjRecognizeMux( Aig_Obj_t * pNode, Aig_Obj_t ** ppNodeT, Aig_Obj_t ** ppNodeE )
{
    Aig_Obj_t * pNode0, * pNode1;
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_ObjIsMuxType(pNode) );
    // get children
    pNode0 = Aig_ObjFanin0(pNode);
    pNode1 = Aig_ObjFanin1(pNode);

    // find the control variable
    if ( Aig_ObjFanin1(pNode0) == Aig_ObjFanin1(pNode1) && (Aig_ObjFaninC1(pNode0) ^ Aig_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Aig_ObjFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Aig_Not(Aig_ObjChild0(pNode0));//pNode1->p1);
            return Aig_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Aig_Not(Aig_ObjChild0(pNode1));//pNode2->p1);
            return Aig_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    else if ( Aig_ObjFanin0(pNode0) == Aig_ObjFanin0(pNode1) && (Aig_ObjFaninC0(pNode0) ^ Aig_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Aig_ObjFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Aig_Not(Aig_ObjChild1(pNode0));//pNode1->p2);
            return Aig_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Aig_Not(Aig_ObjChild1(pNode1));//pNode2->p2);
            return Aig_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Aig_ObjFanin0(pNode0) == Aig_ObjFanin1(pNode1) && (Aig_ObjFaninC0(pNode0) ^ Aig_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Aig_ObjFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Aig_Not(Aig_ObjChild1(pNode0));//pNode1->p2);
            return Aig_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Aig_Not(Aig_ObjChild0(pNode1));//pNode2->p1);
            return Aig_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Aig_ObjFanin1(pNode0) == Aig_ObjFanin0(pNode1) && (Aig_ObjFaninC1(pNode0) ^ Aig_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Aig_ObjFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Aig_Not(Aig_ObjChild0(pNode0));//pNode1->p1);
            return Aig_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Aig_Not(Aig_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Aig_Not(Aig_ObjChild1(pNode1));//pNode2->p2);
            return Aig_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Prints node in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjPrintVerbose( Aig_Obj_t * pObj, int fHaig )
{
    assert( !Aig_IsComplement(pObj) );
    printf( "Node %p : ", pObj );
    if ( Aig_ObjIsConst1(pObj) )
        printf( "constant 1" );
    else if ( Aig_ObjIsPi(pObj) )
        printf( "PI" );
    else
        printf( "AND( %p%s, %p%s )", 
            Aig_ObjFanin0(pObj), (Aig_ObjFaninC0(pObj)? "\'" : " "), 
            Aig_ObjFanin1(pObj), (Aig_ObjFaninC1(pObj)? "\'" : " ") );
    printf( " (refs = %3d)", Aig_ObjRefs(pObj) );
}

/**Function*************************************************************

  Synopsis    [Prints node in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManPrintVerbose( Aig_Man_t * p, int fHaig )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    printf( "PIs: " );
    Aig_ManForEachPi( p, pObj, i )
        printf( " %p", pObj );
    printf( "\n" );
    vNodes = Aig_ManDfs( p );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Aig_ObjPrintVerbose( pObj, fHaig ), printf( "\n" );
    printf( "\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


