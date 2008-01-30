/**CFile****************************************************************

  FileName    [decAbc.c]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Interface between the decomposition package and ABC network.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: decAbc.c,v 1.1 2003/05/22 19:20:05 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transforms the decomposition graph into the AIG.]

  Description [AIG nodes for the fanins should be assigned to pNode->pFunc
  of the leaves of the graph before calling this procedure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Dec_GraphToNetwork( Abc_Aig_t * pMan, Dec_Graph_t * pGraph )
{
    Abc_Obj_t * pAnd0, * pAnd1;
    Dec_Node_t * pNode;
    int i;
    // check for constant function
    if ( Dec_GraphIsConst(pGraph) )
        return Abc_ObjNotCond( Abc_AigConst1(pMan), Dec_GraphIsComplement(pGraph) );
    // check for a literal
    if ( Dec_GraphIsVar(pGraph) )
        return Abc_ObjNotCond( Dec_GraphVar(pGraph)->pFunc, Dec_GraphIsComplement(pGraph) );
    // build the AIG nodes corresponding to the AND gates of the graph
    Dec_GraphForEachNode( pGraph, pNode, i )
    {
        pAnd0 = Abc_ObjNotCond( Dec_GraphNode(pGraph, pNode->eEdge0.Node)->pFunc, pNode->eEdge0.fCompl ); 
        pAnd1 = Abc_ObjNotCond( Dec_GraphNode(pGraph, pNode->eEdge1.Node)->pFunc, pNode->eEdge1.fCompl ); 
        pNode->pFunc = Abc_AigAnd( pMan, pAnd0, pAnd1 );
    }
    // complement the result if necessary
    return Abc_ObjNotCond( pNode->pFunc, Dec_GraphIsComplement(pGraph) );
}

/**Function*************************************************************

  Synopsis    [Counts the number of new nodes added when using this graph.]

  Description [AIG nodes for the fanins should be assigned to pNode->pFunc 
  of the leaves of the graph before calling this procedure. 
  Returns -1 if the number of nodes and levels exceeded the given limit or 
  the number of levels exceeded the maximum allowed level.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dec_GraphToNetworkCount( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int NodeMax, int LevelMax )
{
    Abc_Aig_t * pMan = pRoot->pNtk->pManFunc;
    Dec_Node_t * pNode, * pNode0, * pNode1;
    Abc_Obj_t * pAnd, * pAnd0, * pAnd1;
    int i, Counter, LevelNew, LevelOld;
    // check for constant function or a literal
    if ( Dec_GraphIsConst(pGraph) || Dec_GraphIsVar(pGraph) )
        return 0;
    // set the levels of the leaves
    Dec_GraphForEachLeaf( pGraph, pNode, i )
        pNode->Level = Abc_ObjRegular(pNode->pFunc)->Level;
    // compute the AIG size after adding the internal nodes
    Counter = 0;
    Dec_GraphForEachNode( pGraph, pNode, i )
    {
        // get the children of this node
        pNode0 = Dec_GraphNode( pGraph, pNode->eEdge0.Node );
        pNode1 = Dec_GraphNode( pGraph, pNode->eEdge1.Node );
        // get the AIG nodes corresponding to the children 
        pAnd0 = pNode0->pFunc; 
        pAnd1 = pNode1->pFunc; 
        if ( pAnd0 && pAnd1 )
        {
            // if they are both present, find the resulting node
            pAnd0 = Abc_ObjNotCond( pAnd0, pNode->eEdge0.fCompl );
            pAnd1 = Abc_ObjNotCond( pAnd1, pNode->eEdge1.fCompl );
            pAnd  = Abc_AigAndLookup( pMan, pAnd0, pAnd1 );
            // return -1 if the node is the same as the original root
            if ( Abc_ObjRegular(pAnd) == pRoot )
                return -1;
        }
        else
            pAnd = NULL;
        // count the number of added nodes
        if ( pAnd == NULL || Abc_NodeIsTravIdCurrent(Abc_ObjRegular(pAnd)) )
        {
            if ( ++Counter > NodeMax )
                return -1;
        }
        // count the number of new levels
        LevelNew = 1 + ABC_MAX( pNode0->Level, pNode1->Level );
        if ( pAnd )
        {
            if ( Abc_ObjRegular(pAnd) == Abc_AigConst1(pMan) )
                LevelNew = 0;
            else if ( Abc_ObjRegular(pAnd) == Abc_ObjRegular(pAnd0) )
                LevelNew = (int)Abc_ObjRegular(pAnd0)->Level;
            else if ( Abc_ObjRegular(pAnd) == Abc_ObjRegular(pAnd1) )
                LevelNew = (int)Abc_ObjRegular(pAnd1)->Level;
            LevelOld = (int)Abc_ObjRegular(pAnd)->Level;
            assert( LevelNew == LevelOld );
        }
        if ( LevelNew > LevelMax )
            return -1;
        pNode->pFunc = pAnd;
        pNode->Level = LevelNew;
    }
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Replaces MFFC of the node by the new factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dec_GraphUpdateNetwork( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int nGain )
{
    Abc_Obj_t * pRootNew;
    Abc_Ntk_t * pNtk = pRoot->pNtk;
    int nNodesNew, nNodesOld;
    nNodesOld = Abc_NtkNodeNum(pNtk);
    // create the new structure of nodes
    pRootNew = Dec_GraphToNetwork( pNtk->pManFunc, pGraph );
    // remove the old nodes
    Abc_AigReplace( pNtk->pManFunc, pRoot, pRootNew );
    // compare the gains
    nNodesNew = Abc_NtkNodeNum(pNtk);
    assert( nGain <= nNodesOld - nNodesNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


