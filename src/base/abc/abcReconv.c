/**CFile****************************************************************

  FileName    [abcRes.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Reconvergence=driven cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRes.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct Abc_ManCut_t_
{
    // user specified parameters
    int              nNodeSizeMax;  // the limit on the size of the supernode
    int              nConeSizeMax;  // the limit on the size of the containing cone
    // internal parameters
    Vec_Ptr_t *      vFaninsNode;   // fanins of the supernode
    Vec_Ptr_t *      vFaninsCone;   // fanins of the containing cone
    Vec_Ptr_t *      vVisited;      // the visited nodes
};

static int   Abc_NodeFindCut_int( Vec_Ptr_t * vFanins, int nSizeLimit );
static void  Abc_NodesMarkCollect_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vVisited );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Unmarks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_NodesMark( Vec_Ptr_t * vVisited )
{
    Abc_Obj_t * pNode;
    int i;
    Vec_PtrForEachEntry( vVisited, pNode, i )
        pNode->fMarkA = 1;
}

/**Function*************************************************************

  Synopsis    [Unmarks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_NodesUnmark( Vec_Ptr_t * vVisited )
{
    Abc_Obj_t * pNode;
    int i;
    Vec_PtrForEachEntry( vVisited, pNode, i )
        pNode->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Unmarks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_NodesUnmarkBoth( Vec_Ptr_t * vVisited )
{
    Abc_Obj_t * pNode;
    int i;
    Vec_PtrForEachEntry( vVisited, pNode, i )
        pNode->fMarkA = pNode->fMarkB = 0;
}

/**Function*************************************************************

  Synopsis    [Evaluate the fanin cost.]

  Description [Returns the number of fanins that will be brought in.
  Returns large number if the node cannot be added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_NodeGetFaninCost( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i;
    assert( pNode->fMarkA == 1 );  // this node is in the TFI
    assert( pNode->fMarkB == 1 );  // this node is in the constructed cone
    // check the PI node
    if ( Abc_ObjIsCi(pNode) )
        return 999;
    // skip nodes with many fanouts
    if ( Abc_ObjFanoutNum(pNode) > 5 )
        return 999;
    // check the fanouts
    Abc_ObjForEachFanout( pNode, pFanout, i )
        if ( pFanout->fMarkA && pFanout->fMarkB == 0 ) // the fanout is in the TFI but not in the cone
            return 999;
    // the fanouts are in the TFI and inside the constructed cone
    // return the number of fanins that will be on the boundary if this node is added
    return (!Abc_ObjFanin0(pNode)->fMarkB) + (!Abc_ObjFanin1(pNode)->fMarkB);
}


/**Function*************************************************************

  Synopsis    [Finds a fanin-limited, reconvergence-driven cut for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeFindCut( Abc_ManCut_t * p, Abc_Obj_t * pRoot, bool fContain )
{
    Abc_Obj_t * pNode;
    int i;

    assert( !Abc_ObjIsComplement(pRoot) );
    assert( Abc_ObjIsNode(pRoot) );

    // mark TFI using fMarkA
    Vec_PtrClear( p->vVisited );
    Abc_NodesMarkCollect_rec( pRoot, p->vVisited );

    // start the cut 
    Vec_PtrClear( p->vFaninsNode );
    Vec_PtrPush( p->vFaninsNode, Abc_ObjFanin0(pRoot) );
    Vec_PtrPush( p->vFaninsNode, Abc_ObjFanin1(pRoot) );
    pRoot->fMarkB = 1;
    Abc_ObjFanin0(pRoot)->fMarkB = 1;
    Abc_ObjFanin1(pRoot)->fMarkB = 1;

    // compute the cut
    while ( Abc_NodeFindCut_int( p->vFaninsNode, p->nNodeSizeMax ) );
    assert( Vec_PtrSize(p->vFaninsNode) <= p->nNodeSizeMax );

    // return if containing cut is not requested
    if ( !fContain )
    {
        // unmark TFI using fMarkA and fMarkB
        Abc_NodesUnmarkBoth( p->vVisited );
        return p->vFaninsNode;
    }

    // compute the containing cut
    assert( p->nNodeSizeMax < p->nConeSizeMax );
    // copy the current boundary
    Vec_PtrClear( p->vFaninsCone );
    Vec_PtrForEachEntry( p->vFaninsNode, pNode, i )
        Vec_PtrPush( p->vFaninsCone, pNode );
    // compute the containing cut
    while ( Abc_NodeFindCut_int( p->vFaninsCone, p->nConeSizeMax ) );
    assert( Vec_PtrSize(p->vFaninsCone) <= p->nConeSizeMax );
    // unmark TFI using fMarkA and fMarkB
    Abc_NodesUnmarkBoth( p->vVisited );
    return p->vFaninsNode;
}

/**Function*************************************************************

  Synopsis    [Finds a reconvergence-driven cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeFindCut_int( Vec_Ptr_t * vFanins, int nSizeLimit )
{
    Abc_Obj_t * pNode, * pFaninBest, * pNext;
    int CostBest, CostCur, i;
//    int fFlagProb = (rand() & 1);
    int fFlagProb = 1;
    // find the best fanin
    CostBest   = 100;
    pFaninBest = NULL;
    if ( fFlagProb )
    {
        Vec_PtrForEachEntry( vFanins, pNode, i )
        {
            CostCur = Abc_NodeGetFaninCost( pNode );
            if ( CostBest > CostCur )
            {
                CostBest   = CostCur;
                pFaninBest = pNode;
            }
        }
    }
    else
    {
        Vec_PtrForEachEntry( vFanins, pNode, i )
        {
            CostCur = Abc_NodeGetFaninCost( pNode );
            if ( CostBest >= CostCur )
            {
                CostBest   = CostCur;
                pFaninBest = pNode;
            }
        }
    }
    if ( pFaninBest == NULL )
        return 0;
    assert( CostBest < 3 );
    if ( vFanins->nSize - 1 + CostBest > nSizeLimit )
        return 0;
    assert( Abc_ObjIsNode(pFaninBest) );
    // remove the node from the array
    Vec_PtrRemove( vFanins, pFaninBest );
    // add the left child to the fanins
    pNext = Abc_ObjFanin0(pFaninBest);
    if ( !pNext->fMarkB )
    {
        pNext->fMarkB = 1;
        Vec_PtrPush( vFanins, pNext );
    }
    // add the right child to the fanins
    pNext = Abc_ObjFanin1(pFaninBest);
    if ( !pNext->fMarkB )
    {
        pNext->fMarkB = 1;
        Vec_PtrPush( vFanins, pNext );
    }
    assert( vFanins->nSize <= nSizeLimit );
    // keep doing this
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodesMarkCollect_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vVisited )
{
    if ( pNode->fMarkA == 1 )
        return;
    // visit transitive fanin 
    if ( Abc_ObjIsNode(pNode) )
    {
        Abc_NodesMarkCollect_rec( Abc_ObjFanin0(pNode), vVisited );
        Abc_NodesMarkCollect_rec( Abc_ObjFanin1(pNode), vVisited );
    }
    assert( pNode->fMarkA == 0 );
    pNode->fMarkA = 1;
    Vec_PtrPush( vVisited, pNode );
}


/**Function*************************************************************

  Synopsis    [Returns BDD representing the logic function of the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NodeConeBdd( DdManager * dd, DdNode ** pbVars, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Ptr_t * vVisited )
{
    DdNode * bFunc0, * bFunc1, * bFunc;
    int i;
    // mark the fanins of the cone
    Abc_NodesMark( vFanins );
    // collect the nodes in the DFS order
    Vec_PtrClear( vVisited );
    Abc_NodesMarkCollect_rec( pNode, vVisited );
    // unmark both sets
    Abc_NodesUnmark( vFanins );
    Abc_NodesUnmark( vVisited );
    // set the elementary BDDs
    Vec_PtrForEachEntry( vFanins, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)pbVars[i];
    // compute the BDDs for the collected nodes
    Vec_PtrForEachEntry( vVisited, pNode, i )
    {
        bFunc0 = Cudd_NotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
        bFunc1 = Cudd_NotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) );
        bFunc  = Cudd_bddAnd( dd, bFunc0, bFunc1 );    Cudd_Ref( bFunc );
        pNode->pCopy = (Abc_Obj_t *)bFunc;
    }
    Cudd_Ref( bFunc );
    // dereference the intermediate ones
    Vec_PtrForEachEntry( vVisited, pNode, i )
        Cudd_RecursiveDeref( dd, (DdNode *)pNode->pCopy );
    Cudd_Deref( bFunc );
    return bFunc;
}

/**Function*************************************************************

  Synopsis    [Returns BDD representing the transition relation of the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NodeConeDcs( DdManager * dd, DdNode ** pbVarsX, DdNode ** pbVarsY, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vRoots, Vec_Ptr_t * vVisited )
{
    DdNode * bFunc0, * bFunc1, * bFunc, * bTrans, * bTemp, * bCube, * bResult;
    Abc_Obj_t * pNode;
    int i;
    // mark the fanins of the cone
    Abc_NodesMark( vLeaves );
    // collect the nodes in the DFS order
    Vec_PtrClear( vVisited );
    Vec_PtrForEachEntry( vRoots, pNode, i )
        Abc_NodesMarkCollect_rec( pNode, vVisited );
    // unmark both sets
    Abc_NodesUnmark( vLeaves );
    Abc_NodesUnmark( vVisited );
    // set the elementary BDDs
    Vec_PtrForEachEntry( vLeaves, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)pbVarsX[i];
    // compute the BDDs for the collected nodes
    Vec_PtrForEachEntry( vVisited, pNode, i )
    {
        bFunc0 = Cudd_NotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
        bFunc1 = Cudd_NotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) );
        bFunc  = Cudd_bddAnd( dd, bFunc0, bFunc1 );    Cudd_Ref( bFunc );
        pNode->pCopy = (Abc_Obj_t *)bFunc;
    }
    // compute the transition relation of the cone
    bTrans = b1;    Cudd_Ref( bTrans );
    Vec_PtrForEachEntry( vRoots, pNode, i )
    {
        bFunc = Cudd_bddXnor( dd, (DdNode *)pNode->pCopy, pbVarsY[i] );  Cudd_Ref( bFunc );
        bTrans = Cudd_bddAnd( dd, bTemp = bTrans, bFunc );               Cudd_Ref( bTrans );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bFunc );
    }
    // dereference the intermediate ones
    Vec_PtrForEachEntry( vVisited, pNode, i )
        Cudd_RecursiveDeref( dd, (DdNode *)pNode->pCopy );
    // compute don't-cares
    bCube = Extra_bddComputeRangeCube( dd, vRoots->nSize, vRoots->nSize + vLeaves->nSize );  Cudd_Ref( bCube );
    bResult = Cudd_bddExistAbstract( dd, bTrans, bCube );                Cudd_Ref( bResult );
    bResult = Cudd_Not( bResult );
    Cudd_RecursiveDeref( dd, bCube );
    Cudd_RecursiveDeref( dd, bTrans );
    Cudd_Deref( bResult );
    return bResult;
}
 
/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManCut_t * Abc_NtkManCutStart( int nNodeSizeMax, int nConeSizeMax )
{
    Abc_ManCut_t * p;
    p = ALLOC( Abc_ManCut_t, 1 );
    memset( p, 0, sizeof(Abc_ManCut_t) );
    p->vFaninsNode  = Vec_PtrAlloc( 100 );
    p->vFaninsCone  = Vec_PtrAlloc( 100 );
    p->vVisited     = Vec_PtrAlloc( 100 );
    p->nNodeSizeMax = nNodeSizeMax;
    p->nConeSizeMax = nConeSizeMax;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkManCutStop( Abc_ManCut_t * p )
{
    Vec_PtrFree( p->vFaninsNode );
    Vec_PtrFree( p->vFaninsCone );
    Vec_PtrFree( p->vVisited    );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns the leaves of the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkManCutReadLeaves( Abc_ManCut_t * p )
{
    return p->vFaninsCone;
}



/**Function*************************************************************

  Synopsis    [Collects the TFO of the cut in the topological order.]

  Description [TFO of the cut is defined as a set of nodes, for which the cut
  is a cut, that is, every path from the collected nodes to the CIs goes through 
  a node in the cut. The nodes are collected if their level does not exceed
  the given number (LevelMax). The nodes are returned in the topological order.
  If the root node is given, its MFFC is marked, so that the collected nodes
  do not contain any nodes in the MFFC.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeCollectTfoCands( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, 
    Vec_Ptr_t * vFanins, int LevelMax, Vec_Vec_t * vLevels, Vec_Ptr_t * vResult )
{
    Vec_Ptr_t * vVec;
    Abc_Obj_t * pNode, * pFanout;
    int i, k, v, LevelMin;
    assert( Abc_NtkIsStrash(pNtk) );

    // assuming that the structure is clean
    Vec_VecForEachLevel( vLevels, vVec, i )
        assert( vVec->nSize == 0 );

    // put fanins into the structure while labeling them
    Abc_NtkIncrementTravId( pNtk );
    LevelMin = ABC_INFINITY;
    Vec_PtrForEachEntry( vFanins, pNode, i )
    {
        if ( pNode->Level > (unsigned)LevelMax )
            continue;
        Abc_NodeSetTravIdCurrent( pNode );
        Vec_VecPush( vLevels, pNode->Level, pNode );
        if ( LevelMin < (int)pNode->Level )
            LevelMin = pNode->Level;
    }
    assert( LevelMin >= 0 );

    // mark MFFC 
    if ( pRoot )
        Abc_NodeMffcLabel( pRoot );

    // go through the levels up
    Vec_PtrClear( vResult );
    Vec_VecForEachEntryStartStop( vLevels, pNode, i, k, LevelMin, LevelMax )
    {
        // if the node is not marked, it is not a fanin
        if ( !Abc_NodeIsTravIdCurrent(pNode) )
        {
            // check if it belongs to the TFO
            if ( !Abc_NodeIsTravIdCurrent(Abc_ObjFanin0(pNode)) || 
                 !Abc_NodeIsTravIdCurrent(Abc_ObjFanin1(pNode)) )
                 continue;
            // save the node in the TFO and label it
            Vec_PtrPush( vResult, pNode );
            Abc_NodeSetTravIdCurrent( pNode );
        }
        // go through the fanouts and add them to the structure if they meet the conditions
        Abc_ObjForEachFanout( pNode, pFanout, v )
        {
            // skip if fanout is a CO or its level exceeds
            if ( Abc_ObjIsCo(pFanout) || pFanout->Level > (unsigned)LevelMax )
                continue;
            // skip if it is already added or if it is in MFFC
            if ( Abc_NodeIsTravIdCurrent(pFanout) )
                continue;
            // add it to the structure but do not mark it (until tested later)
            Vec_VecPush( vLevels, pFanout->Level, pFanout );
        }
    }

    // clear the levelized structure
    Vec_VecForEachLevelStartStop( vLevels, vVec, i, LevelMin, LevelMax )
        Vec_PtrClear( vVec );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


