/**CFile****************************************************************

  FileName    [rwrMffc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Procedures working with Maximum Fanout-Free Cones.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrMffc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int  Aig_NodeDeref_rec( Aig_Node_t * pNode );
extern int  Aig_NodeRef_rec( Aig_Node_t * pNode );
extern void Aig_NodeMffsConeSupp( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp );
extern void Aig_NodeFactorConeSupp( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_MffcTest( Aig_Man_t * pMan )
{
    Aig_Node_t * pNode, * pNodeA, * pNodeB, * pNodeC, * pLeaf;
    Vec_Ptr_t * vCone, * vSupp;
    int i, k;//, nNodes1, nNodes2;
    int nSizes = 0;
    int nCones = 0;
    int nMuxes = 0;
    int nExors = 0;

    vCone = Vec_PtrAlloc( 100 );
    vSupp = Vec_PtrAlloc( 100 );

    // mark the multiple-fanout nodes
    Aig_ManForEachAnd( pMan, pNode, i )
        if ( pNode->nRefs > 1 )
            pNode->fMarkA = 1;
    // unmark the control inputs of MUXes and inputs of EXOR gates
    Aig_ManForEachAnd( pMan, pNode, i )
    {
        if ( !Aig_NodeIsMuxType(pNode) )
            continue;

        pNodeC = Aig_NodeRecognizeMux( pNode, &pNodeA, &pNodeB );
        // if real children are used, skip
        if ( Aig_NodeFanin0(pNode)->nRefs > 1 || Aig_NodeFanin1(pNode)->nRefs > 1 )
            continue;
/*

        if ( pNodeC->nRefs == 2 )
            pNodeC->fMarkA = 0;
        if ( Aig_Regular(pNodeA) == Aig_Regular(pNodeB) && Aig_Regular(pNodeA)->nRefs == 2 )
            Aig_Regular(pNodeA)->fMarkA = 0;
*/

        if ( Aig_Regular(pNodeA) == Aig_Regular(pNodeB) )
            nExors++;
        else
            nMuxes++;
    }
    // mark the PO drivers
    Aig_ManForEachPo( pMan, pNode, i )
    {
        Aig_NodeFanin0(pNode)->fMarkA = 1;
        Aig_NodeFanin0(pNode)->fMarkB = 1;
    }


    // print sizes of MFFCs
    Aig_ManForEachAnd( pMan, pNode, i )
    {
        if ( !pNode->fMarkA )
            continue;

//        nNodes1 = Aig_NodeDeref_rec( pNode );
//        Aig_NodeMffsConeSupp( pNode, vCone, vSupp );
//        nNodes2 = Aig_NodeRef_rec( pNode );
//        assert( nNodes1 == nNodes2 );

        Aig_NodeFactorConeSupp( pNode, vCone, vSupp );

        printf( "%6d : Fan = %4d. Co = %5d.  Su = %5d.  %s ", 
            pNode->Id, pNode->nRefs, Vec_PtrSize(vCone), Vec_PtrSize(vSupp), pNode->fMarkB? "po" : "  " );

        Vec_PtrForEachEntry( vSupp, pLeaf, k )
            printf( " %d", pLeaf->Id );

        printf( "\n" );

        nSizes += Vec_PtrSize(vCone);
        nCones++;
    }
    printf( "Nodes = %6d.  MFFC sizes = %6d.  Cones = %6d.  nExors = %6d.  Muxes = %6d.\n",
        Aig_ManAndNum(pMan), nSizes, nCones, nExors, nMuxes );

    // unmark the nodes
    Aig_ManForEachNode( pMan, pNode, i )
    {
        pNode->fMarkA = 0;
        pNode->fMarkB = 0;
        pNode->fMarkC = 0;
    }

    Vec_PtrFree( vCone );
    Vec_PtrFree( vSupp );
}

/**Function*************************************************************

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeDeref_rec( Aig_Node_t * pNode )
{
    Aig_Node_t * pNode0, * pNode1;
    int Counter = 1;
    if ( Aig_NodeIsPi(pNode) )
        return 0;
    pNode0 = Aig_NodeFanin0(pNode);
    pNode1 = Aig_NodeFanin1(pNode);
    assert( pNode0->nRefs > 0 );
    assert( pNode1->nRefs > 0 );
    if ( --pNode0->nRefs == 0 )
        Counter += Aig_NodeDeref_rec( pNode0 );
    if ( --pNode1->nRefs == 0 )
        Counter += Aig_NodeDeref_rec( pNode1 );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeRef_rec( Aig_Node_t * pNode )
{
    Aig_Node_t * pNode0, * pNode1;
    int Counter = 1;
    if ( Aig_NodeIsPi(pNode) )
        return 0;
    pNode0 = Aig_NodeFanin0(pNode);
    pNode1 = Aig_NodeFanin1(pNode);
    if ( pNode0->nRefs++ == 0 )
        Counter += Aig_NodeRef_rec( pNode0 );
    if ( pNode1->nRefs++ == 0 )
        Counter += Aig_NodeRef_rec( pNode1 );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collects the internal and leaf nodes in the derefed MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeMffsConeSupp_rec( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp, int fTopmost )
{
    // skip visited nodes
    if ( Aig_NodeIsTravIdCurrent(pNode) )
        return;
    Aig_NodeSetTravIdCurrent(pNode);
    // add to the new support nodes
    if ( !fTopmost && (Aig_NodeIsPi(pNode) || pNode->nRefs > 0) )
    {
        Vec_PtrPush( vSupp, pNode );
        return;
    }
    // recur on the children
    Aig_NodeMffsConeSupp_rec( Aig_NodeFanin0(pNode), vCone, vSupp, 0 );
    Aig_NodeMffsConeSupp_rec( Aig_NodeFanin1(pNode), vCone, vSupp, 0 );
    // collect the internal node
    Vec_PtrPush( vCone, pNode );
}

/**Function*************************************************************

  Synopsis    [Collects the support of the derefed MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeMffsConeSupp( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp )
{
    assert( Aig_NodeIsAnd(pNode) );
    assert( !Aig_IsComplement(pNode) );
    Vec_PtrClear( vCone );
    Vec_PtrClear( vSupp );
    Aig_ManIncrementTravId( pNode->pMan );
    Aig_NodeMffsConeSupp_rec( pNode, vCone, vSupp, 1 );
}





/**Function*************************************************************

  Synopsis    [Collects the internal and leaf nodes of the factor-cut of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeFactorConeSupp_rec( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp, int fTopmost )
{
    // skip visited nodes
    if ( Aig_NodeIsTravIdCurrent(pNode) )
        return;
    Aig_NodeSetTravIdCurrent(pNode);
    // add to the new support nodes
    if ( !fTopmost && (Aig_NodeIsPi(pNode) || pNode->fMarkA) )
    {
        Vec_PtrPush( vSupp, pNode );
        return;
    }
    // recur on the children
    Aig_NodeFactorConeSupp_rec( Aig_NodeFanin0(pNode), vCone, vSupp, 0 );
    Aig_NodeFactorConeSupp_rec( Aig_NodeFanin1(pNode), vCone, vSupp, 0 );
    // collect the internal node
    assert( fTopmost || !pNode->fMarkA );
    Vec_PtrPush( vCone, pNode );

    assert( pNode->fMarkC == 0 );
    pNode->fMarkC = 1;
}

/**Function*************************************************************

  Synopsis    [Collects the support of the derefed MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeFactorConeSupp( Aig_Node_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp )
{
    assert( Aig_NodeIsAnd(pNode) );
    assert( !Aig_IsComplement(pNode) );
    Vec_PtrClear( vCone );
    Vec_PtrClear( vSupp );
    Aig_ManIncrementTravId( pNode->pMan );
    Aig_NodeFactorConeSupp_rec( pNode, vCone, vSupp, 1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


