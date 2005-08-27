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

static Vec_Int_t * Rwr_NodePreprocess( Rwr_Man_t * p, Rwr_Node_t * pNode );
static int         Rwr_TravCollect_rec( Rwr_Man_t * p, Rwr_Node_t * pNode, Vec_Int_t * vForm );
static void        Rwr_FactorVerify( Vec_Int_t * vForm, unsigned uTruth );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

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
    p->vClasses = Vec_VecStart( 222 );
    for ( i = 0; i < p->nFuncs; i++ )
    {
        if ( p->pTable[i] == NULL )
            continue;
        // consider all implementations of this function
        for ( pNode = p->pTable[i]; pNode; pNode = pNode->pNext )
        {
            assert( pNode->uTruth == p->pTable[i]->uTruth );
            assert( p->pMap[pNode->uTruth] >= 0 && p->pMap[pNode->uTruth] < 222 );
            Vec_VecPush( p->vClasses, p->pMap[pNode->uTruth], pNode );
        }
    }
    // compute decomposition forms for each node
    Vec_VecForEachEntry( p->vClasses, pNode, i, k )
        pNode->pNext = (Rwr_Node_t *)Rwr_NodePreprocess( p, pNode );
}

/**Function*************************************************************

  Synopsis    [Preprocesses subgraphs rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwr_NodePreprocess( Rwr_Man_t * p, Rwr_Node_t * pNode )
{
    Vec_Int_t * vForm;
    int i, Root;
    // consider constant
    if ( pNode->uTruth == 0 )
        return Ft_FactorConst( 0 );
    // consider the case of elementary var
    if ( pNode->uTruth == 0x00FF )
        return Ft_FactorVar( 3, 4, 1 );
    // start the factored form
    vForm = Vec_IntAlloc( 10 );
    for ( i = 0; i < 4; i++ )
        Vec_IntPush( vForm, 0 );
    // collect the nodes
    Rwr_ManIncTravId( p );
    Root = Rwr_TravCollect_rec( p, pNode, vForm );
    if ( Root & 1 )
        Ft_FactorComplement( vForm );
    // verify the factored form
    Rwr_FactorVerify( vForm, pNode->uTruth );
    return vForm;
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

  Synopsis    [Verifies the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_FactorVerify( Vec_Int_t * vForm, unsigned uTruthGold )
{
    Ft_Node_t * pFtNode;
    Vec_Int_t * vTruths;
    unsigned uTruth, uTruth0, uTruth1;
    int i;

    vTruths = Vec_IntAlloc( vForm->nSize );
    Vec_IntPush( vTruths, 0xAAAA );
    Vec_IntPush( vTruths, 0xCCCC );
    Vec_IntPush( vTruths, 0xF0F0 );
    Vec_IntPush( vTruths, 0xFF00 );

    assert( Ft_FactorGetNumVars( vForm ) == 4 );
    for ( i = 4; i < vForm->nSize; i++ )
    {
        pFtNode = Ft_NodeRead( vForm, i );
        // make sure there are no elementary variables
        assert( pFtNode->iFanin0 != pFtNode->iFanin1 );

        uTruth0 = vTruths->pArray[pFtNode->iFanin0];
        uTruth0 = pFtNode->fCompl0? ~uTruth0 : uTruth0;

        uTruth1 = vTruths->pArray[pFtNode->iFanin1];
        uTruth1 = pFtNode->fCompl1? ~uTruth1 : uTruth1;

        uTruth = uTruth0 & uTruth1;
        Vec_IntPush( vTruths, uTruth );
    }
    // complement if necessary
    if ( pFtNode->fCompl )
        uTruth = ~uTruth;
    uTruth &= 0xFFFF;
    if ( uTruth != uTruthGold )
        printf( "Verification failed\n" );
    Vec_IntFree( vTruths );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


