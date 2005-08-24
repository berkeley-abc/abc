/**CFile****************************************************************

  FileName    [rwrDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Evaluation and decomposition procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Int_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Rwr_Cut_t * pCut, int NodeMax, int LevelMax );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs rewriting for one node.]

  Description [This procedure considers all the cuts computed for the node
  and tries to rewrite each of them using the "forest" of different AIG
  structures precomputed and stored in the RWR manager. 
  Determines the best rewriting and computes the gain in the number of AIG
  nodes in the final network. In the end, p->vFanins contains information 
  about the best cut that can be used for rewriting, while p->vForm gives 
  the decomposition tree (represented using factored form data structure).
  Returns gain in the number of nodes or -1 if node cannot be rewritten.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_NodeRewrite( Rwr_Man_t * p, Abc_Obj_t * pNode )
{
    Vec_Int_t * vForm;
    Rwr_Cut_t * pCut;
    int Required, nNodesSaved;
    int i, BestGain = -1;
    // compute the cuts for this node
    Rwr_NodeComputeCuts( p, pNode );
    // get the required times
    Required = Vec_IntEntry( p->vReqTimes, pNode->Id );
    // label MFFC with current ID
    nNodesSaved = Abc_NodeMffcLabel( pNode );
    // go through the cuts
    for ( pCut = (Rwr_Cut_t *)pNode->pCopy, pCut = pCut->pNext; pCut; pCut = pCut->pNext )
    {
        // evaluate the cut
        vForm = Rwr_CutEvaluate( p, pNode, pCut, nNodesSaved, Required );
        // check if the cut is better than the currently best one
        if ( vForm != NULL && BestGain < (int)pCut->Volume )
        {
            assert( pCut->Volume >= 0 );
            BestGain  = pCut->Volume;
            // save this form
            p->vForm = vForm;
            // collect fanins
            Vec_PtrClear( p->vFanins );
            for ( i = 0; i < (int)pCut->nLeaves; i++ )
                Vec_PtrPush( p->vFanins, pCut->ppLeaves[i] );
        }
    }
    return BestGain;
}

/**Function*************************************************************

  Synopsis    [Evaluates the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Rwr_Cut_t * pCut, int NodeMax, int LevelMax )
{
    Vec_Ptr_t Vector = {0,0,0}, * vFanins = &Vector;
    Vec_Ptr_t * vSubgraphs;
    Vec_Int_t * vFormBest;
    Rwr_Node_t * pNode;
    int GainCur, GainBest = -1, i;
    // find the matching class of subgraphs
    vSubgraphs = Vec_VecEntry( p->vClasses, p->pMap[pCut->uTruth] );
    // determine the best subgraph
    Vec_PtrForEachEntry( vSubgraphs, pNode, i )
    {
        // create the fanin array
        vFanins->nSize  = pCut->nLeaves;
        vFanins->pArray = pCut->ppLeaves;
        // detect how many unlabeled nodes will be reused
        GainCur = Abc_NodeStrashDecCount( pRoot->pNtk->pManFunc,  pRoot, vFanins, (Vec_Int_t *)pNode->pNext, 
            p->vLevNums, NodeMax, LevelMax );
        if ( GainBest < GainCur )
        {
            GainBest  = GainCur;
            vFormBest = (Vec_Int_t *)pNode->pNext;
        }
    }
    if ( GainBest == -1 )
        return NULL;
    pCut->Volume = GainBest;
    return vFormBest;
}


/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_TravCollect_rec( Rwr_Man_t * p, Rwr_Node_t * pNode, Vec_Int_t * vForm )
{
    Ft_Node_t Node, NodeA, NodeB;
    int Node0, Node1;
    // elementary variable
    if ( pNode->fUsed )
        return ((pNode->Id - 1) << 1); 
    // previously visited node
    if ( pNode->TravId == p->nTravIds )
        return pNode->Volume;
    pNode->TravId = p->nTravIds;
    // solve for children
    Node0 = Rwr_TravCollect_rec( p, Rwr_Regular(pNode->p0), vForm );
    Node1 = Rwr_TravCollect_rec( p, Rwr_Regular(pNode->p1), vForm );
    // create the decomposition node(s)
    if ( pNode->fExor )
    {
        assert( !Rwr_IsComplement(pNode->p0) );
        assert( !Rwr_IsComplement(pNode->p1) );
        NodeA.fIntern = 1;
        NodeA.fConst  = 0;
        NodeA.fCompl  = 0;
        NodeA.fCompl0 = !(Node0 & 1);
        NodeA.fCompl1 =  (Node1 & 1);
        NodeA.iFanin0 = (Node0 >> 1);
        NodeA.iFanin1 = (Node1 >> 1);
        Vec_IntPush( vForm, Ft_Node2Int(NodeA) );

        NodeB.fIntern = 1;
        NodeB.fConst  = 0;
        NodeB.fCompl  = 0;
        NodeB.fCompl0 =  (Node0 & 1);
        NodeB.fCompl1 = !(Node1 & 1);
        NodeB.iFanin0 = (Node0 >> 1);
        NodeB.iFanin1 = (Node1 >> 1);
        Vec_IntPush( vForm, Ft_Node2Int(NodeB) );

        Node.fIntern = 1;
        Node.fConst  = 0;
        Node.fCompl  = 0;
        Node.fCompl0 = 1;
        Node.fCompl1 = 1;
        Node.iFanin0 = vForm->nSize - 2;
        Node.iFanin1 = vForm->nSize - 1;
        Vec_IntPush( vForm, Ft_Node2Int(Node) );
    }
    else
    {
        Node.fIntern = 1;
        Node.fConst  = 0;
        Node.fCompl  = 0;
        Node.fCompl0 = Rwr_IsComplement(pNode->p0) ^ (Node0 & 1);
        Node.fCompl1 = Rwr_IsComplement(pNode->p1) ^ (Node1 & 1);
        Node.iFanin0 = (Node0 >> 1);
        Node.iFanin1 = (Node1 >> 1);
        Vec_IntPush( vForm, Ft_Node2Int(Node) );
    }
    // save the number of this node
    pNode->Volume = ((vForm->nSize - 1) << 1) | pNode->fExor;
    return pNode->Volume;
}

/**Function*************************************************************

  Synopsis    [Preprocesses subgraphs rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_NodePreprocess( Rwr_Man_t * p, Rwr_Node_t * pNode )
{
    Vec_Int_t * vForm;
    int i, Root;
    vForm = Vec_IntAlloc( 10 );
    for ( i = 0; i < 5; i++ )
        Vec_IntPush( vForm, 0 );
    // collect the nodes
    Rwr_ManIncTravId( p );
    Root = Rwr_TravCollect_rec( p, pNode, vForm );
    if ( Root & 1 )
        Ft_FactorComplement( vForm );
    pNode->pNext = (Rwr_Node_t *)vForm;
}

/**Function*************************************************************

  Synopsis    [Preprocesses computed library of subgraphs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPreprocess( Rwr_Man_t * p )
{
    Rwr_Node_t * pNode;
    int i, k;
    // put the nodes into the structure
    p->vClasses = Vec_VecAlloc( 222 );
    for ( i = 0; i < p->nFuncs; i++ )
        for ( pNode = p->pTable[i]; pNode; pNode = pNode->pNext )
            Vec_VecPush( p->vClasses, p->pMap[pNode->uTruth], pNode );
    // compute decomposition forms for each node
    Vec_VecForEachEntry( p->vClasses, pNode, i, k )
        Rwr_NodePreprocess( p, pNode );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


