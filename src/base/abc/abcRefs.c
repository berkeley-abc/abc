/**CFile****************************************************************

  FileName    [abcRefs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures using reference counting of the AIG nodes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRefs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fReference, bool fLabel, Vec_Ptr_t * vNodes );
static int Abc_NodeRefDerefStop( Abc_Obj_t * pNode, bool fReference );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the MFFC size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcSize( Abc_Obj_t * pNode )
{
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    if ( Abc_ObjFaninNum(pNode) == 0 )
        return 0;
    nConeSize1 = Abc_NodeRefDeref( pNode, 0, 0, NULL ); // dereference
    nConeSize2 = Abc_NodeRefDeref( pNode, 1, 0, NULL ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [Returns the MFFC size while stopping at the complemented edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcSizeStop( Abc_Obj_t * pNode )
{
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    if ( Abc_ObjFaninNum(pNode) == 0 )
        return 0;
    nConeSize1 = Abc_NodeRefDerefStop( pNode, 0 ); // dereference
    nConeSize2 = Abc_NodeRefDerefStop( pNode, 1 ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [Labels MFFC with the current traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcLabel( Abc_Obj_t * pNode )
{
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    if ( Abc_ObjFaninNum(pNode) == 0 )
        return 0;
    nConeSize1 = Abc_NodeRefDeref( pNode, 0, 1, NULL ); // dereference
    nConeSize2 = Abc_NodeRefDeref( pNode, 1, 0, NULL ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in MFFC in the topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeMffcCollect( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    vNodes = Vec_PtrAlloc( 8 );
    if ( Abc_ObjFaninNum(pNode) == 0 )
        return vNodes;
    nConeSize1 = Abc_NodeRefDeref( pNode, 0, 0, vNodes ); // dereference
    nConeSize2 = Abc_NodeRefDeref( pNode, 1, 0, NULL );   // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [References/references the node and returns MFFC size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fReference, bool fLabel, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pNode0, * pNode1;
    int Counter;
    // label visited nodes
    if ( fLabel )
        Abc_NodeSetTravIdCurrent( pNode );
    // collect visited nodes
    if ( vNodes )
        Vec_PtrPush( vNodes, pNode );
    // skip the CI
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    // process the internal node
    pNode0 = Abc_ObjFanin0(pNode);
    pNode1 = Abc_ObjFanin1(pNode);
    Counter = 1;
    if ( fReference )
    {
        if ( pNode0->vFanouts.nSize++ == 0 )
            Counter += Abc_NodeRefDeref( pNode0, fReference, fLabel, vNodes );
        if ( pNode1->vFanouts.nSize++ == 0 )
            Counter += Abc_NodeRefDeref( pNode1, fReference, fLabel, vNodes );
    }
    else
    {
        assert( pNode0->vFanouts.nSize > 0 );
        assert( pNode1->vFanouts.nSize > 0 );
        if ( --pNode0->vFanouts.nSize == 0 )
            Counter += Abc_NodeRefDeref( pNode0, fReference, fLabel, vNodes );
        if ( --pNode1->vFanouts.nSize == 0 )
            Counter += Abc_NodeRefDeref( pNode1, fReference, fLabel, vNodes );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [References/references the node and returns MFFC size.]

  Description [Stops at the complemented edges.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeRefDerefStop( Abc_Obj_t * pNode, bool fReference )
{
    Abc_Obj_t * pNode0, * pNode1;
    int Counter;
    // skip the CI
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    // process the internal node
    pNode0 = Abc_ObjFanin0(pNode);
    pNode1 = Abc_ObjFanin1(pNode);
    Counter = 1;
    if ( fReference )
    {
        if ( pNode0->vFanouts.nSize++ == 0 && !Abc_ObjFaninC0(pNode) )
            Counter += Abc_NodeRefDerefStop( pNode0, fReference );
        if ( pNode1->vFanouts.nSize++ == 0 && !Abc_ObjFaninC1(pNode) )
            Counter += Abc_NodeRefDerefStop( pNode1, fReference );
    }
    else
    {
        assert( pNode0->vFanouts.nSize > 0 );
        assert( pNode1->vFanouts.nSize > 0 );
        if ( --pNode0->vFanouts.nSize == 0 && !Abc_ObjFaninC0(pNode) )
            Counter += Abc_NodeRefDerefStop( pNode0, fReference );
        if ( --pNode1->vFanouts.nSize == 0 && !Abc_ObjFaninC1(pNode) )
            Counter += Abc_NodeRefDerefStop( pNode1, fReference );
    }
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


