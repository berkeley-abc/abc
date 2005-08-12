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

static int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fFanouts, bool fReference );

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
    nConeSize2 = Abc_NodeRefDeref( pNode, 0, 1 ); // reference
    assert( nConeSize1 == nConeSize2 );
    assert( nConeSize1 > 0 );
    return nConeSize1;
}

/**Function*************************************************************

  Synopsis    [Procedure returns the size of the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMffcRemove( Abc_Obj_t * pNode )
{
    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode( pNode ) );
    return Abc_NodeRefDeref( pNode, 1, 0 ); // dereference
}

/**Function*************************************************************

  Synopsis    [References/references the node and returns MFFC size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fFanouts, bool fReference )
{
    Abc_Obj_t * pNode0, * pNode1;
    int Counter;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    pNode0 = Abc_ObjFanin( pNode, 0 );
    pNode1 = Abc_ObjFanin( pNode, 1 );
    Counter = 1;
    if ( fReference )
    {
        if ( pNode0->vFanouts.nSize++ == 0 )
        {
            Counter += Abc_NodeRefDeref( pNode0, fFanouts, fReference );
            if ( fFanouts )  
                Abc_ObjAddFanin( pNode, pNode0 );
        }
        if ( pNode1->vFanouts.nSize++ == 0 )
        {
            Counter += Abc_NodeRefDeref( pNode1, fFanouts, fReference );
            if ( fFanouts )  
                Abc_ObjAddFanin( pNode, pNode1 );
        }
    }
    else
    {
        assert( pNode0->vFanouts.nSize > 0 );
        assert( pNode1->vFanouts.nSize > 0 );
        if ( --pNode0->vFanouts.nSize == 0 )
        {
            Counter += Abc_NodeRefDeref( pNode0, fFanouts, fReference );
            if ( fFanouts )  
                Abc_ObjDeleteFanin( pNode, pNode0 );
        }
        if ( --pNode1->vFanouts.nSize == 0 )
        {
            Counter += Abc_NodeRefDeref( pNode1, fFanouts, fReference );
            if ( fFanouts )  
                Abc_ObjDeleteFanin( pNode, pNode1 );
        }
    }
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


