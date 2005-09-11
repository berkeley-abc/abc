/**CFile****************************************************************

  FileName    [abcForBack.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simple forward/backward retiming procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcForBack.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs forward retiming of the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeForward( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pFanout;
    int i, k, nLatches;
    assert( Abc_NtkIsSeq( pNtk ) );
    // assume that all nodes can be retimed
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            continue;
        Vec_PtrPush( vNodes, pNode );
        pNode->fMarkA = 1;
    }
    // process the nodes
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
//        printf( "(%d,%d) ", Abc_ObjFaninL0(pNode), Abc_ObjFaninL0(pNode) );
        // get the number of latches to retime
        nLatches = Abc_ObjFaninLMin(pNode);
        if ( nLatches == 0 )
            continue;
        assert( nLatches > 0 );
        // subtract these latches on the fanin side
        Abc_ObjAddFaninL0( pNode, -nLatches );
        Abc_ObjAddFaninL1( pNode, -nLatches );
        // add these latches on the fanout size
        Abc_ObjForEachFanout( pNode, pFanout, k )
        {
            Abc_ObjAddFanoutL( pNode, pFanout, nLatches );
            if ( pFanout->fMarkA == 0 )
            {   // schedule the node for updating
                Vec_PtrPush( vNodes, pFanout );
                pFanout->fMarkA = 1;
            }
        }
        // unmark the node as processed
        pNode->fMarkA = 0;
    }
    Vec_PtrFree( vNodes );
    // clean the marks
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pNode->fMarkA = 0;
        if ( Abc_NodeIsConst(pNode) )
            continue;
        assert( Abc_ObjFaninLMin(pNode) == 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Performs forward retiming of the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeBackward( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pFanin, * pFanout;
    int i, k, nLatches;
    assert( Abc_NtkIsSeq( pNtk ) );
    // assume that all nodes can be retimed
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            continue;
        Vec_PtrPush( vNodes, pNode );
        pNode->fMarkA = 1;
    }
    // process the nodes
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        // get the number of latches to retime
        nLatches = Abc_ObjFanoutLMin(pNode);
        if ( nLatches == 0 )
            continue;
        assert( nLatches > 0 );
        // subtract these latches on the fanout side
        Abc_ObjForEachFanout( pNode, pFanout, k )
            Abc_ObjAddFanoutL( pNode, pFanout, -nLatches );
        // add these latches on the fanin size
        Abc_ObjForEachFanin( pNode, pFanin, k )
        {
            Abc_ObjAddFaninL( pNode, k, nLatches );
            if ( Abc_ObjIsPi(pFanin) || Abc_NodeIsConst(pFanin) )
                continue;
            if ( pFanin->fMarkA == 0 )
            {   // schedule the node for updating
                Vec_PtrPush( vNodes, pFanin );
                pFanin->fMarkA = 1;
            }
        }
        // unmark the node as processed
        pNode->fMarkA = 0;
    }
    Vec_PtrFree( vNodes );
    // clean the marks
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pNode->fMarkA = 0;
        if ( Abc_NodeIsConst(pNode) )
            continue;
//        assert( Abc_ObjFanoutLMin(pNode) == 0 );
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


