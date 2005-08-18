/**CFile****************************************************************

  FileName    [abcRefs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Reference counting of the nodes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRefs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fReference, bool fLabel );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Procedure returns the size of the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcSize( Abc_Obj_t * pNode )
{
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    nConeSize1 = Abc_NodeRefDeref( pNode, 0, 0 ); // dereference
    nConeSize2 = Abc_NodeRefDeref( pNode, 1, 0 ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [Lavels MFFC with the current traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcLabel( Abc_Obj_t * pNode )
{
    int nConeSize1, nConeSize2;
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    nConeSize1 = Abc_NodeRefDeref( pNode, 0, 0 ); // dereference
    nConeSize2 = Abc_NodeRefDeref( pNode, 1, 1 ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [References/references the node and returns MFFC size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fReference, bool fLabel )
{
    Abc_Obj_t * pNode0, * pNode1;
    int Counter;
    if ( fLabel )
        Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    pNode0 = Abc_ObjFanin( pNode, 0 );
    pNode1 = Abc_ObjFanin( pNode, 1 );
    Counter = 1;
    if ( fReference )
    {
        if ( pNode0->vFanouts.nSize++ == 0 )
            Counter += Abc_NodeRefDeref( pNode0, fReference, fLabel );
        if ( pNode1->vFanouts.nSize++ == 0 )
            Counter += Abc_NodeRefDeref( pNode1, fReference, fLabel );
    }
    else
    {
        assert( pNode0->vFanouts.nSize > 0 );
        assert( pNode1->vFanouts.nSize > 0 );
        if ( --pNode0->vFanouts.nSize == 0 )
            Counter += Abc_NodeRefDeref( pNode0, fReference, fLabel );
        if ( --pNode1->vFanouts.nSize == 0 )
            Counter += Abc_NodeRefDeref( pNode1, fReference, fLabel );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Replaces MFFC of the node by the new factored.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeUpdate( Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Int_t * vForm, int nGain )
{
    Abc_Obj_t * pNodeNew;
    int nNodesNew, nNodesOld;
    nNodesOld = Abc_NtkNodeNum(pNode->pNtk);
    // create the new structure of nodes
    assert( Vec_PtrSize(vFanins) < Vec_IntSize(vForm) );
    pNodeNew = Abc_NodeStrashDec( pNode->pNtk->pManFunc, vFanins, vForm );
    // remove the old nodes
    Abc_AigReplace( pNode->pNtk->pManFunc, pNode, pNodeNew );
    // compare the gains
    nNodesNew = Abc_NtkNodeNum(pNode->pNtk);
    assert( nGain <= nNodesOld - nNodesNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


