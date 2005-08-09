/**CFile****************************************************************

  FileName    [abcDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures that use depth-first search.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_NtkDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void Abc_AigDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static int  Abc_NtkGetLevelNum_rec( Abc_Obj_t * pNode );
static bool Abc_NtkIsAcyclic_rec( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving out PIs, POs and latches.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkDfs( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNet, * pNode;
    int i, fMadeComb;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fMadeComb = Abc_NtkMakeComb( pNtk );
        Abc_NtkForEachPo( pNtk, pNet, i )
        {
            if ( Abc_ObjIsCi(pNet) )
                continue;
            Abc_NtkDfs_rec( Abc_ObjFanin0(pNet), vNodes );
        }
        if ( fMadeComb )  Abc_NtkMakeSeq( pNtk );
    }
    else
    {
        Abc_NtkForEachCo( pNtk, pNode, i )
            Abc_NtkDfs_rec( Abc_ObjFanin0(pNode), vNodes );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving out PIs, POs and latches.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkDfsNodes( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppNodes, int nNodes )
{
    Vec_Ptr_t * vNodes;
    int i, fMadeComb;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fMadeComb = Abc_NtkMakeComb( pNtk );
        for ( i = 0; i < nNodes; i++ )
            Abc_NtkDfs_rec( ppNodes[i], vNodes );
        if ( fMadeComb )  
            Abc_NtkMakeSeq( pNtk );
    }
    else
    {
        for ( i = 0; i < nNodes; i++ )
            if ( Abc_ObjIsCo(ppNodes[i]) )
                Abc_NtkDfs_rec( Abc_ObjFanin0(ppNodes[i]), vNodes );
            else if ( Abc_ObjIsNode(ppNodes[i]) )
                Abc_NtkDfs_rec( ppNodes[i], vNodes );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( !Abc_ObjIsComplement( pNode ) );

    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );

    // skip the PI
    if ( Abc_ObjIsPi(pNode) || Abc_ObjIsLatch(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );

    // visit the transitive fanin of the node
    if ( Abc_NtkIsNetlist(pNode->pNtk) )
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( Abc_ObjIsCi(pFanin) )
                continue;
            pFanin = Abc_ObjFanin0(pFanin);
            Abc_NtkDfs_rec( pFanin, vNodes );
        }
    }
    else
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
            Abc_NtkDfs_rec( pFanin, vNodes );
    }
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}


/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving out PIs, POs and latches.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_AigDfs( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsAig(pNtk) );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    Abc_NtkForEachCo( pNtk, pNode, i )
        Abc_AigDfs_rec( Abc_ObjFanin0(pNode), vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( !Abc_ObjIsComplement( pNode ) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // skip the PI
    if ( Abc_ObjIsPi(pNode) || Abc_ObjIsLatch(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_AigDfs_rec( pFanin, vNodes );
    // visit the equivalent nodes
    if ( Abc_NodeIsChoice( pNode ) )
        for ( pFanin = pNode->pData; pFanin; pFanin = pFanin->pData )
            Abc_AigDfs_rec( pFanin, vNodes );
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the DFS manner by level.]

  Description [The number of levels should be set!!!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_DfsLevelizedTfo_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vLevels )
{
    Abc_Obj_t * pFanout;
    int i;

    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );

    // skip the terminals
    if ( Abc_ObjIsTerm(pNode) || Abc_ObjIsLatch(pNode) )
        return;
    assert( Abc_ObjIsNode(pNode) );

    // add the node to the structure
    if ( vLevels->nSize <= (int)pNode->Level )
    {
        Vec_PtrGrow( vLevels, pNode->Level + 1 );
        for ( i = vLevels->nSize; i <= (int)pNode->Level; i++ )
            vLevels->pArray[i] = Vec_PtrAlloc( 16 );
        vLevels->nSize = pNode->Level + 1;
    }
    Vec_PtrPush( vLevels->pArray[pNode->Level], pNode );

    // visit the TFO
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Abc_DfsLevelizedTfo_rec( pFanout, vLevels );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the DFS manner by level.]

  Description [The number of levels should be set!!!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_DfsLevelized( Abc_Obj_t * pNode, bool fTfi )
{
    Vec_Ptr_t * vLevels;
    Abc_Obj_t * pFanout;
    int i;
    assert( fTfi == 0 );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNode->pNtk );
    vLevels = Vec_PtrAlloc( 100 );
    if ( Abc_ObjIsNode(pNode) )
        Abc_DfsLevelizedTfo_rec( pNode, vLevels );
    else
        Abc_ObjForEachFanout( pNode, pFanout, i )
            Abc_DfsLevelizedTfo_rec( pFanout, vLevels );
    return vLevels;
}


/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetLevelNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNet, * pNode, * pDriver;
    unsigned LevelsMax;
    int i, fMadeComb;
    
    // set the traversal ID for this traversal
    Abc_NtkIncrementTravId( pNtk );
    // perform the traversal
    LevelsMax = 0;
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fMadeComb = Abc_NtkMakeComb( pNtk );
        Abc_NtkForEachPo( pNtk, pNet, i )
        {
            if ( Abc_ObjIsCi(pNet) )
                continue;
            pDriver = Abc_ObjFanin0( pNet );
            Abc_NtkGetLevelNum_rec( pDriver );
            if ( LevelsMax < pDriver->Level )
                LevelsMax = pDriver->Level;
        }
        if ( fMadeComb )  Abc_NtkMakeSeq( pNtk );
    }
    else
    {
//        Abc_NtkForEachCo( pNtk, pNode, i )
        Abc_NtkForEachNode( pNtk, pNode, i )
        {
//            pDriver = Abc_ObjFanin0( pNode );
            pDriver = pNode;

            Abc_NtkGetLevelNum_rec( pDriver );
            if ( LevelsMax < pDriver->Level )
                LevelsMax = pDriver->Level;
        }
    }
    return LevelsMax;
}

/**Function*************************************************************

  Synopsis    [Recursively counts the number of logic levels of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetLevelNum_rec( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( !Abc_ObjIsComplement( pNode ) );
    // skip the PI
    if ( Abc_ObjIsPi(pNode) || Abc_ObjIsLatch(pNode) )
        return 0;
    assert( Abc_ObjIsNode( pNode ) );

    // if this node is already visited, return
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return pNode->Level;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );

    // visit the transitive fanin
    pNode->Level = 0;
    if ( Abc_NtkIsNetlist(pNode->pNtk) )
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( Abc_ObjIsCi(pFanin) )
                continue;
            pFanin = Abc_ObjFanin0(pFanin);
            Abc_NtkGetLevelNum_rec( pFanin );
            if ( pNode->Level < pFanin->Level )
                pNode->Level = pFanin->Level;
        }
    }
    else
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            Abc_NtkGetLevelNum_rec( pFanin );
            if ( pNode->Level < pFanin->Level )
                pNode->Level = pFanin->Level;
        }
    }
    pNode->Level++;
    return pNode->Level;
}


/**Function*************************************************************

  Synopsis    [Detects combinational loops.]

  Description [This procedure is based on the idea suggested by Donald Chai. 
  As we traverse the network and visit the nodes, we need to distinquish 
  three types of nodes: (1) those that are visited for the first time, 
  (2) those that have been visited in this traversal but are currently not 
  on the traversal path, (3) those that have been visited and are currently 
  on the travesal path. When the node of type (3) is encountered, it means 
  that there is a combinational loop. To mark the three types of nodes, 
  two new values of the traversal IDs are used.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkIsAcyclic( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNet, * pNode;
    int fAcyclic, fMadeComb, i;
    // set the traversal ID for this DFS ordering
    Abc_NtkIncrementTravId( pNtk );   
    Abc_NtkIncrementTravId( pNtk );   
    // pNode->TravId == pNet->nTravIds      means "pNode is on the path"
    // pNode->TravId == pNet->nTravIds - 1  means "pNode is visited but is not on the path"
    // pNode->TravId < pNet->nTravIds - 1   means "pNode is not visited"
    // traverse the network to detect cycles
    fAcyclic = 1;
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fMadeComb = Abc_NtkMakeComb( pNtk );
        Abc_NtkForEachPo( pNtk, pNet, i )
        {
            if ( Abc_ObjIsCi(pNet) )
                continue;
            pNode = Abc_ObjFanin0( pNet );
            if ( Abc_NodeIsTravIdPrevious(pNode) )
                continue;
            // traverse the output logic cone to detect the combinational loops
            if ( (fAcyclic = Abc_NtkIsAcyclic_rec( pNode )) == 0 ) 
            { // stop as soon as the first loop is detected
                fprintf( stdout, " (the output node)\n" );
                break;
            }
        }
        if ( fMadeComb )  Abc_NtkMakeSeq( pNtk );
    }
    else
    {
        Abc_NtkForEachCo( pNtk, pNode, i )
        {
            pNode = Abc_ObjFanin0( pNode );
            if ( Abc_NodeIsTravIdPrevious(pNode) )
                continue;
            // traverse the output logic cone to detect the combinational loops
            if ( (fAcyclic = Abc_NtkIsAcyclic_rec( pNode )) == 0 ) 
            { // stop as soon as the first loop is detected
                fprintf( stdout, " (the output node)\n" );
                break;
            }
        }
    }
    return fAcyclic;
}

/**Function*************************************************************

  Synopsis    [Recursively detects combinational loops.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkIsAcyclic_rec( Abc_Obj_t * pNode )
{
    Abc_Ntk_t * pNtk = pNode->pNtk;
    Abc_Obj_t * pFanin;
    int fAcyclic, i;

    assert( !Abc_ObjIsComplement( pNode ) );
    // skip the PI
    if ( Abc_ObjIsPi(pNode) || Abc_ObjIsLatch(pNode) )
        return 1;
    assert( Abc_ObjIsNode( pNode ) );

    // make sure the node is not visited
    assert( !Abc_NodeIsTravIdPrevious(pNode) );
    // check if the node is part of the combinational loop
    if ( Abc_NodeIsTravIdCurrent(pNode) )
    {
        fprintf( stdout, "Network \"%s\" contains combinational loop!\n", pNtk->pName );
        fprintf( stdout, "Node \"%s\" is encountered twice on the following path:\n", Abc_ObjName(pNode) );
        fprintf( stdout, " %s", Abc_ObjName(pNode) );
        return 0;
    }
    // mark this node as a node on the current path
    Abc_NodeSetTravIdCurrent( pNode );

    // visit the transitive fanin
    if ( Abc_NtkIsNetlist(pNode->pNtk) )
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            if ( Abc_ObjIsCi(pFanin) )
                continue;
            pFanin = Abc_ObjFanin0(pFanin);
            // make sure there is no mixing of networks
            assert( pFanin->pNtk == pNode->pNtk );
            // check if the fanin is visited
            if ( Abc_NodeIsTravIdPrevious(pFanin) ) 
                continue;
            // traverse searching for the loop
            fAcyclic = Abc_NtkIsAcyclic_rec( pFanin );
            // return as soon as the loop is detected
            if ( fAcyclic == 0 ) 
            {
                fprintf( stdout, "  <--  %s", Abc_ObjName(pNode) );
                return 0;
            }
        }
    }
    else
    {
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            // make sure there is no mixing of networks
            assert( pFanin->pNtk == pNode->pNtk );
            // check if the fanin is visited
            if ( Abc_NodeIsTravIdPrevious(pFanin) ) 
                continue;
            // traverse searching for the loop
            fAcyclic = Abc_NtkIsAcyclic_rec( pFanin );
            // return as soon as the loop is detected
            if ( fAcyclic == 0 ) 
            {
                fprintf( stdout, "  <--  %s", Abc_ObjName(pNode) );
                return 0;
            }
        }
    }
    // mark this node as a visited node
    Abc_NodeSetTravIdPrevious( pNode );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


