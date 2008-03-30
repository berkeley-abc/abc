/**CFile****************************************************************

  FileName    [nwkDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Logic network representation.]

  Synopsis    [DFS traversals.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description [Assumes that white boxes have unit level.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManLevel( Nwk_Man_t * pNtk )
{
    Tim_Man_t * pManTimeUnit;
    Nwk_Obj_t * pObj, * pFanin;
    int i, k, LevelMax, Level;
    // clean the levels
    Nwk_ManForEachObj( pNtk, pObj, i )
        Nwk_ObjSetLevel( pObj, 0 );
    // perform level computation
    LevelMax = 0;
    pManTimeUnit = pNtk->pManTime ? Tim_ManDupUnit( pNtk->pManTime ) : NULL;
    if ( pManTimeUnit )
        Tim_ManIncrementTravId( pManTimeUnit );
    Nwk_ManForEachObj( pNtk, pObj, i )
    {
        if ( Nwk_ObjIsCi(pObj) )
        {
            Level = pManTimeUnit? (int)Tim_ManGetPiArrival( pManTimeUnit, pObj->PioId ) : 0;
            Nwk_ObjSetLevel( pObj, Level );
        }
        else if ( Nwk_ObjIsCo(pObj) )
        {
            Level = Nwk_ObjLevel( Nwk_ObjFanin0(pObj) );
            if ( pManTimeUnit )
                Tim_ManSetPoArrival( pManTimeUnit, pObj->PioId, (float)Level );
            Nwk_ObjSetLevel( pObj, Level );
            if ( LevelMax < Nwk_ObjLevel(pObj) )
                LevelMax = Nwk_ObjLevel(pObj);
        }
        else if ( Nwk_ObjIsNode(pObj) )
        {
            Level = 0;
            Nwk_ObjForEachFanin( pObj, pFanin, k )
                if ( Level < Nwk_ObjLevel(pFanin) )
                    Level = Nwk_ObjLevel(pFanin);
            Nwk_ObjSetLevel( pObj, Level + 1 );
        }
        else
            assert( 0 );
    }
    // set the old timing manager
    if ( pManTimeUnit )
        Tim_ManStop( pManTimeUnit );
    return LevelMax;
}



/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManLevel2_rec( Nwk_Obj_t * pObj )
{
    Nwk_Obj_t * pNext;
    int i, iBox, iTerm1, nTerms, LevelMax = 0;
    if ( Nwk_ObjIsTravIdCurrent( pObj ) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    if ( Nwk_ObjIsCi(pObj) )
    {
        iBox = Tim_ManBoxForCi( pObj->pMan->pManTime, pObj->PioId );
        if ( iBox >= 0 ) // this is not a true PI
        {
            iTerm1 = Tim_ManBoxInputFirst( pObj->pMan->pManTime, iBox );
            nTerms = Tim_ManBoxInputNum( pObj->pMan->pManTime, iBox );
            for ( i = 0; i < nTerms; i++ )
            {
                pNext = Nwk_ManCo(pObj->pMan, iTerm1 + i);
                Nwk_ManLevel2_rec( pNext );
                if ( LevelMax < Nwk_ObjLevel(pNext) )
                    LevelMax = Nwk_ObjLevel(pNext);
            }
            LevelMax++;
        }
    }
    else if ( Nwk_ObjIsNode(pObj) || Nwk_ObjIsCo(pObj) )
    {
        Nwk_ObjForEachFanin( pObj, pNext, i )
        {
            Nwk_ManLevel2_rec( pNext );
            if ( LevelMax < Nwk_ObjLevel(pNext) )
                LevelMax = Nwk_ObjLevel(pNext);
        }
        if ( Nwk_ObjIsNode(pObj) )
            LevelMax++;
    }
    else
        assert( 0 );
    Nwk_ObjSetLevel( pObj, LevelMax );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManLevel2( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pObj;
    int i, LevelMax = 0;
    Nwk_ManForEachObj( pNtk, pObj, i )
        Nwk_ObjSetLevel( pObj, 0 );
    Nwk_ManIncrementTravId( pNtk );
    Nwk_ManForEachPo( pNtk, pObj, i )
    {
        Nwk_ManLevel2_rec( pObj );
        if ( LevelMax < Nwk_ObjLevel(pObj) )
            LevelMax = Nwk_ObjLevel(pObj);
    }
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Nwk_ManLevelize( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pObj;
    Vec_Vec_t * vLevels;
    int nLevels, i;
    nLevels = Nwk_ManLevel( pNtk );
    vLevels = Vec_VecStart( nLevels + 1 );
    Nwk_ManForEachNode( pNtk, pObj, i )
    {
        assert( (int)pObj->tArrival <= nLevels );
        Vec_VecPush( vLevels, (int)pObj->tArrival, pObj );
    }
    return vLevels;
}



/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManDfs_rec( Nwk_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Nwk_Obj_t * pNext;
    int i;
    if ( Nwk_ObjIsTravIdCurrent( pObj ) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    Nwk_ObjForEachFanin( pObj, pNext, i )
        Nwk_ManDfs_rec( pNext, vNodes );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Nwk_ManDfs( Nwk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Nwk_Obj_t * pObj;
    int i;
    Nwk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Nwk_ManForEachObj( pNtk, pObj, i )
    {
        if ( Nwk_ObjIsCi(pObj) )
        {
            Nwk_ObjSetTravIdCurrent( pObj );
            Vec_PtrPush( vNodes, pObj );
        }
        else if ( Nwk_ObjIsCo(pObj) )
            Nwk_ManDfs_rec( pObj, vNodes );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManDfsNodes_rec( Nwk_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Nwk_Obj_t * pNext;
    int i;
    if ( Nwk_ObjIsTravIdCurrent( pObj ) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    if ( Nwk_ObjIsCi(pObj) )
        return;
    assert( Nwk_ObjIsNode(pObj) );
    Nwk_ObjForEachFanin( pObj, pNext, i )
        Nwk_ManDfsNodes_rec( pNext, vNodes );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Returns the set of internal nodes rooted in the given nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Nwk_ManDfsNodes( Nwk_Man_t * pNtk, Nwk_Obj_t ** ppNodes, int nNodes )
{
    Vec_Ptr_t * vNodes;
    int i;
    // set the traversal ID
    Nwk_ManIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    for ( i = 0; i < nNodes; i++ )
        if ( Nwk_ObjIsCo(ppNodes[i]) )
            Nwk_ManDfsNodes_rec( Nwk_ObjFanin0(ppNodes[i]), vNodes );
        else
            Nwk_ManDfsNodes_rec( ppNodes[i], vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManDfsReverse_rec( Nwk_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Nwk_Obj_t * pNext;
    int i, iBox, iTerm1, nTerms;
    if ( Nwk_ObjIsTravIdCurrent( pObj ) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    if ( Nwk_ObjIsCo(pObj) )
    {
        if ( pObj->pMan->pManTime )
        {
            iBox = Tim_ManBoxForCo( pObj->pMan->pManTime, pObj->PioId );
            if ( iBox >= 0 ) // this is not a true PO
            {
                iTerm1 = Tim_ManBoxOutputFirst( pObj->pMan->pManTime, iBox );
                nTerms = Tim_ManBoxOutputNum( pObj->pMan->pManTime, iBox );
                for ( i = 0; i < nTerms; i++ )
                {
                    pNext = Nwk_ManCi(pObj->pMan, iTerm1 + i);
                    Nwk_ManDfsReverse_rec( pNext, vNodes );
                }
            }
        }
    }
    else if ( Nwk_ObjIsNode(pObj) || Nwk_ObjIsCi(pObj) )
    {
        Nwk_ObjForEachFanout( pObj, pNext, i )
            Nwk_ManDfsReverse_rec( pNext, vNodes );
    }
    else
        assert( 0 );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Nwk_ManDfsReverse( Nwk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Nwk_Obj_t * pObj;
    int i;
    Nwk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Nwk_ManForEachPi( pNtk, pObj, i )
        Nwk_ManDfsReverse_rec( pObj, vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManSupportNodes_rec( Nwk_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Nwk_Obj_t * pFanin;
    int i;
    // if this node is already visited, skip
    if ( Nwk_ObjIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Nwk_ObjSetTravIdCurrent( pNode );
    // collect the CI
    if ( Nwk_ObjIsCi(pNode) )
    {
        Vec_PtrPush( vNodes, pNode );
        return;
    }
    assert( Nwk_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        Nwk_ManSupportNodes_rec( pFanin, vNodes );
}

/**Function*************************************************************

  Synopsis    [Returns the set of CI nodes in the support of the given nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Nwk_ManSupportNodes( Nwk_Man_t * pNtk, Nwk_Obj_t ** ppNodes, int nNodes )
{
    Vec_Ptr_t * vNodes;
    int i;
    // set the traversal ID
    Nwk_ManIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    for ( i = 0; i < nNodes; i++ )
        if ( Nwk_ObjIsCo(ppNodes[i]) )
            Nwk_ManSupportNodes_rec( Nwk_ObjFanin0(ppNodes[i]), vNodes );
        else
            Nwk_ManSupportNodes_rec( ppNodes[i], vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Computes the sum total of supports of all outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManSupportSum( Nwk_Man_t * pNtk )
{
    Vec_Ptr_t * vSupp;
    Nwk_Obj_t * pObj;
    int i, nTotalSupps = 0;
    Nwk_ManForEachCo( pNtk, pObj, i )
    {
        vSupp = Nwk_ManSupportNodes( pNtk, &pObj, 1 );
        nTotalSupps += Vec_PtrSize( vSupp );
        Vec_PtrFree( vSupp );
    }
    printf( "Total supports = %d.\n", nTotalSupps );
}


/**Function*************************************************************

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ObjDeref_rec( Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Nwk_ObjIsCi(pNode) )
        return 0;
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        assert( pFanin->nFanouts > 0 );
        if ( --pFanin->nFanouts == 0 )
            Counter += Nwk_ObjDeref_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ObjRef_rec( Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Nwk_ObjIsCi(pNode) )
        return 0;
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( pFanin->nFanouts++ == 0 )
            Counter += Nwk_ObjRef_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collects the internal and boundary nodes in the derefed MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ObjMffcLabel_rec( Nwk_Obj_t * pNode, int fTopmost )
{
    Nwk_Obj_t * pFanin;
    int i;
    // add to the new support nodes
    if ( !fTopmost && (Nwk_ObjIsCi(pNode) || pNode->nFanouts > 0) )
        return;
    // skip visited nodes
    if ( Nwk_ObjIsTravIdCurrent(pNode) )
        return;
    Nwk_ObjSetTravIdCurrent(pNode);
    // recur on the children
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        Nwk_ObjMffcLabel_rec( pFanin, 0 );
    // collect the internal node
//    printf( "%d ", pNode->Id );
}

/**Function*************************************************************

  Synopsis    [Collects the internal nodes of the MFFC limited by cut.]

  Description []
               
  SideEffects [Increments the trav ID and marks visited nodes.]

  SeeAlso     []

***********************************************************************/
int Nwk_ObjMffcLabel( Nwk_Obj_t * pNode )
{
    int Count1, Count2;
    // dereference the node
    Count1 = Nwk_ObjDeref_rec( pNode );
    // collect the nodes inside the MFFC
    Nwk_ManIncrementTravId( pNode->pMan );
    Nwk_ObjMffcLabel_rec( pNode, 1 );
    // reference it back
    Count2 = Nwk_ObjRef_rec( pNode );
    assert( Count1 == Count2 );
    return Count1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


