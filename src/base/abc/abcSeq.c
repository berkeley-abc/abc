/**CFile****************************************************************

  FileName    [abcSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

/*
    A sequential network is an AIG whose edges have number-of-latches attributes, 
    in addition to the complemented attibutes. 

    The sets of PIs/POs remain the same as in logic network. 
    Constant 1 node can only be used as a fanin of a PO node and reset node.
    The reset node producing sequence (01111...) is used to create the
    initialization logic of all latches.
    The latches do not have explicit initial state but they are implicitly
    reset by the reset node.

*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Int_t * Abc_NtkSeqCountLatches( Abc_Ntk_t * pNtk );
static void        Abc_NodeSeqCountLatches( Abc_Obj_t * pObj, Vec_Int_t * vNumbers );

static void        Abc_NtkSeqCreateLatches( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
static void        Abc_NodeSeqCreateLatches( Abc_Obj_t * pObj, int nLatches );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts a normal AIG into a sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAigToSeq( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    assert( Abc_NtkIsAig(pNtk) );
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_SEQ );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts a sequential AIG into a logic SOP network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkSeqToLogicSop( Abc_Ntk_t * pNtk )
{
    int fCheck = 1;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin, * pFaninNew;
    int i, k;
    assert( Abc_NtkIsSeq(pNtk) );
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC_SOP );
    // create the constant and reset nodes
    Abc_NtkDupConst1( pNtk, pNtkNew );
    Abc_NtkDupReset( pNtk, pNtkNew );
    // duplicate the nodes, create node functions and latches
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_NodeIsConst(pObj) )
            continue;
        Abc_NtkDupObj(pNtkNew, pObj);
        pObj->pCopy->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }
    // create latches for the new nodes
    Abc_NtkSeqCreateLatches( pNtk, pNtkNew );
    // connect the objects
    Abc_NtkForEachObj( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            // find the fanin
            pFaninNew = pFanin->pCopy;
            for ( i = 0; i < Abc_ObjFaninL(pObj, k); i++ )
                pFaninNew = pFaninNew->pCopy;
            Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate the EXDC network
    if ( pNtk->pExdc )
        fprintf( stdout, "Warning: EXDC network is not copied.\n" );
    if ( fCheck && !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkSeqToLogic(): Network check has failed.\n" );
    return pNtkNew;
}




/**Function*************************************************************

  Synopsis    [Finds max number of latches on the fanout edges of each node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkSeqCountLatches( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vNumbers;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsSeq( pNtk ) );
    // start the array of counters
    vNumbers = Vec_IntAlloc( 0 );
    Vec_IntFill( vNumbers, Abc_NtkObjNum(pNtk), 0 );
    // count for each edge
    Abc_NtkForEachObj( pNtk, pObj, i )
        Abc_NodeSeqCountLatches( pObj, vNumbers );
    return vNumbers;
}

/**Function*************************************************************

  Synopsis    [Countes the latch numbers due to the fanins edges of the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSeqCountLatches( Abc_Obj_t * pObj, Vec_Int_t * vNumbers )
{
    Abc_Obj_t * pFanin;
    int k, nLatches;
    // go through each fanin edge
    Abc_ObjForEachFanin( pObj, pFanin, k )
    {
        nLatches = Abc_ObjFaninL( pObj, k );
        if ( nLatches == 0 )
            continue;
        if ( Vec_IntEntry( vNumbers, pFanin->Id ) < nLatches )
            Vec_IntWriteEntry( vNumbers, pFanin->Id, nLatches );
    }
}



/**Function*************************************************************

  Synopsis    [Creates latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqCreateLatches( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Vec_Int_t * vNumbers;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsSeq( pNtk ) );
    // create latches for each new object according to the counters
    vNumbers = Abc_NtkSeqCountLatches( pNtk );
    Abc_NtkForEachObj( pNtk, pObj, i )
        Abc_NodeSeqCreateLatches( pObj->pCopy, Vec_IntEntry(vNumbers, pObj->Id) );
    Vec_IntFree( vNumbers );
    // add latch to the PI/PO lists, create latch names
    Abc_NtkFinalizeLatches( pNtkNew );
}

/**Function*************************************************************

  Synopsis    [Creates the given number of latches for this object.]

  Description [The latches are attached to the node and to each other
  through the pCopy field.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSeqCreateLatches( Abc_Obj_t * pObj, int nLatches )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    Abc_Obj_t * pLatch, * pFanin;
    int i;
    pFanin = pObj;
    for ( i = 0, pFanin = pObj; i < nLatches; pFanin = pLatch, i++ )
    {
        pLatch = Abc_NtkCreateLatch( pNtk );
        Abc_ObjAddFanin( pLatch, pFanin );
        pFanin->pCopy = pLatch;
    }
}

/**Function*************************************************************

  Synopsis    [Counters the number of latches in the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSeqLatchNum( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vNumbers;
    Abc_Obj_t * pObj;
    int i, Counter;
    assert( Abc_NtkIsSeq( pNtk ) );
    // create latches for each new object according to the counters
    Counter = 0;
    vNumbers = Abc_NtkSeqCountLatches( pNtk );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        assert( Abc_ObjFanoutLMax(pObj) == Vec_IntEntry(vNumbers, pObj->Id) );
        Counter += Vec_IntEntry(vNumbers, pObj->Id);
    }
    Vec_IntFree( vNumbers );
    return Counter;
}






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
        Vec_PtrPush( vNodes, pNode );
        pNode->fMarkA = 1;
    }
    // process the nodes
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
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
        assert( Abc_ObjFanoutLMin(pNode) == 0 );
    }
}




/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout )
{
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFanin0(pFanout) == pObj )
        return Abc_ObjFaninL0(pFanout);
    else if ( Abc_ObjFanin1(pFanout) == pObj )
        return Abc_ObjFaninL1(pFanout);
    else 
        assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sets the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjSetFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats )  
{ 
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFanin0(pFanout) == pObj )
        Abc_ObjSetFaninL0(pFanout, nLats);
    else if ( Abc_ObjFanin1(pFanout) == pObj )
        Abc_ObjSetFaninL1(pFanout, nLats);
    else 
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Adds to the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjAddFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats )  
{ 
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFanin0(pFanout) == pObj )
        Abc_ObjAddFaninL0(pFanout, nLats);
    else if ( Abc_ObjFanin1(pFanout) == pObj )
        Abc_ObjAddFaninL1(pFanout, nLats);
    else 
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutLMax( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, nLatch, nLatchRes;
    nLatchRes = -1;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( nLatchRes < (nLatch = Abc_ObjFanoutL(pObj, pFanout)) )
            nLatchRes = nLatch;
    assert( nLatchRes >= 0 );
    return nLatchRes;
}

/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutLMin( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, nLatch, nLatchRes;
    nLatchRes = ABC_INFINITY;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( nLatchRes > (nLatch = Abc_ObjFanoutL(pObj, pFanout)) )
            nLatchRes = nLatch;
    assert( nLatchRes < ABC_INFINITY );
    return nLatchRes;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


