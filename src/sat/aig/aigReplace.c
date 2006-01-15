/**CFile****************************************************************

  FileName    [aigUpdate.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigUpdate.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs internal replacement step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_AigReplace_int( Aig_Man_t * pMan, int fUpdateLevel )
{
    Vec_Ptr_t * vFanouts;
    Aig_Node_t * pOld, * pNew, * pFanin0, * pFanin1, * pFanout, * pTemp, * pFanoutNew;
    int k, iFanin;
    // get the pair of nodes to replace
    assert( Vec_PtrSize(pMan->vToReplace) > 0 );
    pNew = Vec_PtrPop( pMan->vToReplace );
    pOld = Vec_PtrPop( pMan->vToReplace );
    // make sure the old node is internal, regular, and has fanouts
    // (the new node can be PI or internal, is complemented, and can have fanouts)
    assert( !Aig_IsComplement(pOld) );
    assert( pOld->nRefs > 0 );
    assert( Aig_NodeIsAnd(pOld) );
    assert( Aig_NodeIsPo(pNew) );
    // look at the fanouts of old node
    vFanouts = Aig_NodeGetFanouts( pOld );
    Vec_PtrForEachEntry( vFanouts, pFanout, k )
    {
        if ( Aig_NodeIsPo(pFanout) )
        {
            // patch the first fanin of the PO
            pFanout->Fans[0].iNode  = Aig_Regular(pNew)->Id;
            pFanout->Fans[0].fComp ^= Aig_IsComplement(pNew);
            continue;
        }
        // find the old node as a fanin of this fanout
        iFanin = Aig_NodeWhatFanin( pFanout, pOld );
        assert( iFanin == 0 || iFanin == 1 );
        // get the new fanin
        pFanin0 = Aig_NotCond( pNew, pFanout->Fans[iFanin].fComp );
        assert( Aig_Regular(pFanin0) != pFanout );
        // get another fanin
        pFanin1 = iFanin? Aig_NodeChild0(pFanout) : Aig_NodeChild1(pFanout);
        assert( Aig_Regular(pFanin1) != pFanout );
        assert( Aig_Regular(pFanin0) != Aig_Regular(pFanin1) );             
        // order them
        if ( Aig_Regular(pFanin0)->Id > Aig_Regular(pFanin1)->Id ) 
            pTemp = pFanin0, pFanin0 = pFanin1, pFanin1 = pTemp;
        // check if the node with these fanins exists
        if ( pFanoutNew = Aig_TableLookupNode( pMan, pFanin0, pFanin1 ) )
        { // such node exists (it may be a constant)
            // schedule replacement of the old fanout by the new fanout
            Vec_PtrPush( pMan->vToReplace, pFanout );
            Vec_PtrPush( pMan->vToReplace, pFanoutNew );
            continue;
        }
        // such node does not exist - modify the old fanout node 
        // (this way the change will not propagate all the way to the COs)
        Aig_NodeDisconnectAnd( pFanout );
        Aig_NodeConnectAnd( pFanin0, pFanin1, pFanout );
        // recreate the old fanout with new fanins and add it to the table
        assert( Aig_NodeIsAcyclic(pFanout, pFanout) );
        // update the level if requested
        if ( fUpdateLevel )
        {
            if ( Aig_NodeUpdateLevel_int(pFanout) )
                pMan->nLevelMax = Aig_ManGetLevelMax( pMan );
            //Aig_NodeGetLevelRNew( pFanout );
            Aig_NodeUpdateLevelR_int( pFanout );
        }
    }
    // if the node has no fanouts left, remove its MFFC
    if ( pOld->nRefs == 0 )
        Aig_NodeDeleteAnd_rec( pMan, pOld );
}

/**Function*************************************************************

  Synopsis    [Replaces one AIG node by the other.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManReplaceNode( Aig_Man_t * pMan, Aig_Node_t * pOld, Aig_Node_t * pNew, int fUpdateLevel )
{
    assert( Vec_PtrSize(pMan->vToReplace) == 0 );
    Vec_PtrPush( pMan->vToReplace, pOld );
    Vec_PtrPush( pMan->vToReplace, pNew );
    while ( Vec_PtrSize(pMan->vToReplace) )
        Abc_AigReplace_int( pMan, fUpdateLevel );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


