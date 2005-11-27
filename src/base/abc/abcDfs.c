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

static void     Abc_NtkDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void     Abc_AigDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void     Abc_NtkDfsReverse_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void     Abc_NtkNodeSupport_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void     Abc_DfsLevelizedTfo_rec( Abc_Obj_t * pNode, Vec_Vec_t * vLevels );
static int      Abc_NtkGetLevelNum_rec( Abc_Obj_t * pNode );
static bool     Abc_NtkIsAcyclic_rec( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving CIs and CO.
  However it marks with the current TravId both CIs and COs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkDfs( Abc_Ntk_t * pNtk, int fCollectAll )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        Abc_NodeSetTravIdCurrent( pObj );
        Abc_NtkDfs_rec( Abc_ObjFanin0Ntk(Abc_ObjFanin0(pObj)), vNodes );
    }
    // collect dangling nodes if asked to
    if ( fCollectAll )
    {
        Abc_NtkForEachNode( pNtk, pObj, i )
            if ( !Abc_NodeIsTravIdCurrent(pObj) )
                Abc_NtkDfs_rec( pObj, vNodes );
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
    int i;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    for ( i = 0; i < nNodes; i++ )
    {
        if ( Abc_ObjIsCo(ppNodes[i]) )
        {
            Abc_NodeSetTravIdCurrent(ppNodes[i]);
            Abc_NtkDfs_rec( Abc_ObjFanin0Ntk(Abc_ObjFanin0(ppNodes[i])), vNodes );
        }
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
    assert( !Abc_ObjIsNet(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // skip the CI
    if ( Abc_ObjIsCi(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkDfs_rec( Abc_ObjFanin0Ntk(pFanin), vNodes );
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}


/**Function*************************************************************

  Synopsis    [Returns the reverse DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving out CIs/COs.
  However it marks both CIs and COs with the current TravId.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkDfsReverse( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanout;
    int i, k;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        Abc_NodeSetTravIdCurrent( pObj );
        pObj = Abc_ObjFanout0Ntk(pObj);
        Abc_ObjForEachFanout( pObj, pFanout, k )
            Abc_NtkDfsReverse_rec( pFanout, vNodes );
    }
    // add constant nodes in the end
    Abc_NtkForEachNode( pNtk, pObj, i )
        if ( Abc_NodeIsConst(pObj) )
            Vec_PtrPush( vNodes, pObj );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDfsReverse_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanout;
    int i;
    assert( !Abc_ObjIsNet(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // skip the CI
    if ( Abc_ObjIsCo(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    pNode = Abc_ObjFanout0Ntk(pNode);
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Abc_NtkDfsReverse_rec( pFanout, vNodes );
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the ordering of nodes is DFS.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkIsDfsOrdered( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pFanin;
    int i, k;
    assert( !Abc_NtkIsSeq(pNtk) );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // mark the CIs
    Abc_NtkForEachCi( pNtk, pNode, i )
        Abc_NodeSetTravIdCurrent( pNode );
    // go through the nodes
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        // check the fanins of the node
        Abc_ObjForEachFanin( pNode, pFanin, k )
            if ( !Abc_NodeIsTravIdCurrent(pFanin) )
                return 0;
        // check the choices of the node
        if ( Abc_NtkIsStrash(pNtk) && Abc_NodeIsAigChoice(pNode) )
            for ( pFanin = pNode->pData; pFanin; pFanin = pFanin->pData )
                if ( !Abc_NodeIsTravIdCurrent(pFanin) )
                    return 0;
        // mark the node as visited
        Abc_NodeSetTravIdCurrent( pNode );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the set of CI nodes in the support of the given nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkNodeSupport( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppNodes, int nNodes )
{
    Vec_Ptr_t * vNodes;
    int i;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    for ( i = 0; i < nNodes; i++ )
        if ( Abc_ObjIsCo(ppNodes[i]) )
            Abc_NtkNodeSupport_rec( Abc_ObjFanin0(ppNodes[i]), vNodes );
        else
            Abc_NtkNodeSupport_rec( ppNodes[i], vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkNodeSupport_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( !Abc_ObjIsNet(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // collect the CI
    if ( Abc_ObjIsCi(pNode) )
    {
        Vec_PtrPush( vNodes, pNode );
        return;
    }
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkNodeSupport_rec( Abc_ObjFanin0Ntk(pFanin), vNodes );
}


/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of logic nodes.]

  Description [Collects only the internal nodes, leaving out CIs/COs.
  However it marks both CIs and COs with the current TravId.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_AigDfs( Abc_Ntk_t * pNtk, int fCollectAll, int fCollectCos )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Abc_AigDfs_rec( Abc_ObjFanin0(pNode), vNodes );
        Abc_NodeSetTravIdCurrent( pNode );
        if ( fCollectCos )
            Vec_PtrPush( vNodes, pNode );
    }
    // collect dangling nodes if asked to
    if ( fCollectAll )
    {
        Abc_NtkForEachNode( pNtk, pNode, i )
            if ( !Abc_NodeIsTravIdCurrent(pNode) )
                Abc_AigDfs_rec( pNode, vNodes );
    }
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
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // skip the PI
    if ( Abc_ObjIsCi(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_AigDfs_rec( pFanin, vNodes );
    // visit the equivalent nodes
    if ( Abc_NodeIsAigChoice( pNode ) )
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
Vec_Vec_t * Abc_DfsLevelized( Abc_Obj_t * pNode, bool fTfi )
{
    Vec_Vec_t * vLevels;
    Abc_Obj_t * pFanout;
    int i;
    assert( fTfi == 0 );
    assert( !Abc_NtkIsNetlist(pNode->pNtk) );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNode->pNtk );
    vLevels = Vec_VecAlloc( 100 );
    if ( Abc_ObjIsNode(pNode) )
        Abc_DfsLevelizedTfo_rec( pNode, vLevels );
    else
    {
        assert( Abc_ObjIsCi(pNode) );
        Abc_NodeSetTravIdCurrent( pNode );
        Abc_ObjForEachFanout( pNode, pFanout, i )
            Abc_DfsLevelizedTfo_rec( pFanout, vLevels );
    }
    return vLevels;
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the DFS manner by level.]

  Description [The number of levels should be set!!!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_DfsLevelizedTfo_rec( Abc_Obj_t * pNode, Vec_Vec_t * vLevels )
{
    Abc_Obj_t * pFanout;
    int i;
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // skip the terminals
    if ( Abc_ObjIsCo(pNode) )
        return;
    assert( Abc_ObjIsNode(pNode) );
    // add the node to the structure
    Vec_VecPush( vLevels, pNode->Level, pNode );
    // visit the TFO
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Abc_DfsLevelizedTfo_rec( pFanout, vLevels );
}


/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetLevelNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, LevelsMax;
    // set the traversal ID for this traversal
    Abc_NtkIncrementTravId( pNtk );
    // set the CI levels to zero
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->Level = 0;
    // perform the traversal
    LevelsMax = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Abc_NtkGetLevelNum_rec( pNode );
        if ( LevelsMax < (int)pNode->Level )
            LevelsMax = (int)pNode->Level;
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
    int i, Level;
    assert( !Abc_ObjIsNet(pNode) );
    // skip the PI
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    assert( Abc_ObjIsNode( pNode ) );
    // if this node is already visited, return
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return pNode->Level;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // visit the transitive fanin
    pNode->Level = 0;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        Level = Abc_NtkGetLevelNum_rec( Abc_ObjFanin0Ntk(pFanin) );
        if ( pNode->Level < (unsigned)Level )
            pNode->Level = Level;
    }
    if ( Abc_ObjFaninNum(pNode) > 0 )
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
    Abc_Obj_t * pNode;
    int fAcyclic, i;
    // set the traversal ID for this DFS ordering
    Abc_NtkIncrementTravId( pNtk );   
    Abc_NtkIncrementTravId( pNtk );   
    // pNode->TravId == pNet->nTravIds      means "pNode is on the path"
    // pNode->TravId == pNet->nTravIds - 1  means "pNode is visited but is not on the path"
    // pNode->TravId <  pNet->nTravIds - 1  means "pNode is not visited"
    // traverse the network to detect cycles
    fAcyclic = 1;
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pNode = Abc_ObjFanin0Ntk(Abc_ObjFanin0(pNode));
        if ( Abc_NodeIsTravIdPrevious(pNode) )
            continue;
        // traverse the output logic cone
        if ( fAcyclic = Abc_NtkIsAcyclic_rec(pNode) )
            continue;
        // stop as soon as the first loop is detected
        fprintf( stdout, " (cone of CO \"%s\")\n", Abc_ObjName(pNode) );
        break;
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
    assert( !Abc_ObjIsNet(pNode) );
    if ( Abc_ObjIsCi(pNode) )
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
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        pFanin = Abc_ObjFanin0Ntk(pFanin);
        // make sure there is no mixing of networks
        assert( pFanin->pNtk == pNode->pNtk );
        // check if the fanin is visited
        if ( Abc_NodeIsTravIdPrevious(pFanin) ) 
            continue;
        // traverse the fanin's cone searching for the loop
        if ( fAcyclic = Abc_NtkIsAcyclic_rec(pFanin) )
            continue;
        // return as soon as the loop is detected
        fprintf( stdout, " <-- %s", Abc_ObjName(pNode) );
        return 0;
    }
    // mark this node as a visited node
    Abc_NodeSetTravIdPrevious( pNode );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Analyses choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeSetChoiceLevel_rec( Abc_Obj_t * pNode, int fMaximum )
{
    Abc_Obj_t * pTemp;
    int Level1, Level2, Level, LevelE;
    // skip the visited node
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return (int)pNode->pCopy;
    Abc_NodeSetTravIdCurrent( pNode );
    // compute levels of the children nodes
    Level1 = Abc_NodeSetChoiceLevel_rec( Abc_ObjFanin0(pNode), fMaximum );
    Level2 = Abc_NodeSetChoiceLevel_rec( Abc_ObjFanin1(pNode), fMaximum );
    Level  = 1 + ABC_MAX( Level1, Level2 );
    if ( pNode->pData )
    {
        LevelE = Abc_NodeSetChoiceLevel_rec( pNode->pData, fMaximum );
        if ( fMaximum )
            Level = ABC_MAX( Level, LevelE );
        else
            Level = ABC_MIN( Level, LevelE );
        // set the level of all equivalent nodes to be the same minimum
        for ( pTemp = pNode->pData; pTemp; pTemp = pTemp->pData )
            pTemp->pCopy = (void *)Level;
    }
    pNode->pCopy = (void *)Level;
    return Level;
}

/**Function*************************************************************

  Synopsis    [Resets the levels of the nodes in the choice graph.]

  Description [Makes the level of the choice nodes to be equal to the
  maximum of the level of the nodes in the equivalence class. This way
  sorting by level leads to the reverse topological order, which is
  needed for the required time computation.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_AigSetChoiceLevels( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, LevelMax, LevelCur;
    assert( Abc_NtkIsStrash(pNtk) );
    // set the new travid counter
    Abc_NtkIncrementTravId( pNtk );
    // set levels of the CI and constant
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        Abc_NodeSetTravIdCurrent( pObj );
        pObj->pCopy = NULL;
    }
    pObj = Abc_NtkConst1( pNtk );
    Abc_NodeSetTravIdCurrent( pObj );
    pObj->pCopy = NULL;
    // set levels of all other nodes
    LevelMax = 0;
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        LevelCur = Abc_NodeSetChoiceLevel_rec( Abc_ObjFanin0(pObj), 1 );
        LevelMax = ABC_MAX( LevelMax, LevelCur );
    }
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Returns nodes by level from the smallest to the largest.]

  Description [Correctly handles the case of choice nodes, by first
  spreading them out across several levels and then collecting.]
               
  SideEffects [What happens with dangling nodes???]

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_AigGetLevelizedOrder( Abc_Ntk_t * pNtk, int fCollectCis )
{
    Vec_Ptr_t * vNodes, * vLevels;
    Abc_Obj_t * pNode, ** ppHead;
    int LevelMax, i;
    assert( Abc_NtkIsStrash(pNtk) );
    // set the correct levels
    Abc_NtkCleanCopy( pNtk );
    LevelMax = Abc_AigSetChoiceLevels( pNtk );
    // relink nodes by level
    vLevels = Vec_PtrStart( LevelMax + 1 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        ppHead = ((Abc_Obj_t **)vLevels->pArray) + (int)pNode->pCopy;
        pNode->pCopy = *ppHead;
        *ppHead = pNode;
    }
    // recollect nodes
    vNodes = Vec_PtrStart( Abc_NtkNodeNum(pNtk) );
    Vec_PtrForEachEntryStart( vLevels, pNode, i, !fCollectCis )
        for ( ; pNode; pNode = pNode->pCopy )
            Vec_PtrPush( vNodes, pNode );
    Vec_PtrFree( vLevels );
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


