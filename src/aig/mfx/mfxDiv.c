/**CFile****************************************************************

  FileName    [mfxDiv.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures to compute candidate divisors.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxDiv.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfxInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Marks and collects the TFI cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MfxWinMarkTfi_rec( Nwk_Obj_t * pObj, Vec_Ptr_t * vCone )
{
    Nwk_Obj_t * pFanin;
    int i;
    if ( Nwk_ObjIsTravIdCurrent(pObj) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    if ( Nwk_ObjIsCi(pObj) )
    {
        Vec_PtrPush( vCone, pObj );
        return;
    }
    assert( Nwk_ObjIsNode(pObj) );
    // visit the fanins of the node
    Nwk_ObjForEachFanin( pObj, pFanin, i )
        Abc_MfxWinMarkTfi_rec( pFanin, vCone );
    Vec_PtrPush( vCone, pObj );
}

/**Function*************************************************************

  Synopsis    [Marks and collects the TFI cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_MfxWinMarkTfi( Nwk_Obj_t * pNode )
{
    Vec_Ptr_t * vCone;
    vCone = Vec_PtrAlloc( 100 );
    Abc_MfxWinMarkTfi_rec( pNode, vCone );
    return vCone;
}

/**Function*************************************************************

  Synopsis    [Marks the TFO of the collected nodes up to the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MfxWinSweepLeafTfo_rec( Nwk_Obj_t * pObj, float tArrivalMax )
{
    Nwk_Obj_t * pFanout;
    int i;
    if ( Nwk_ObjIsCo(pObj) || Nwk_ObjArrival(pObj) > tArrivalMax )
        return;
    if ( Nwk_ObjIsTravIdCurrent(pObj) )
        return;
    Nwk_ObjSetTravIdCurrent( pObj );
    Nwk_ObjForEachFanout( pObj, pFanout, i )
        Abc_MfxWinSweepLeafTfo_rec( pFanout, tArrivalMax );
}

/**Function*************************************************************

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_MfxNodeDeref_rec( Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Nwk_ObjIsCi(pNode) )
        return 0;
    Nwk_ObjSetTravIdCurrent( pNode );
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        assert( pFanin->nFanouts > 0 );
        if ( --pFanin->nFanouts == 0 )
            Counter += Abc_MfxNodeDeref_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_MfxNodeRef_rec( Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Nwk_ObjIsCi(pNode) )
        return 0;
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( pFanin->nFanouts++ == 0 )
            Counter += Abc_MfxNodeRef_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Labels MFFC of the node with the current trav ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_MfxWinVisitMffc( Nwk_Obj_t * pNode )
{
    int Count1, Count2;
    assert( Nwk_ObjIsNode(pNode) );
    // dereference the node (mark with the current trav ID)
    Count1 = Abc_MfxNodeDeref_rec( pNode );
    // reference it back
    Count2 = Abc_MfxNodeRef_rec( pNode );
    assert( Count1 == Count2 );
    return Count1;
}

/**Function*************************************************************

  Synopsis    [Computes divisors and add them to nodes in the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Mfx_ComputeDivisors( Mfx_Man_t * p, Nwk_Obj_t * pNode, float tArrivalMax )
{
    Vec_Ptr_t * vCone, * vDivs;
    Nwk_Obj_t * pObj, * pFanout, * pFanin;
    int k, f, m;
    int nDivsPlus = 0, nTrueSupp;
    assert( p->vDivs == NULL );

    // mark the TFI with the current trav ID
    Nwk_ManIncrementTravId( pNode->pMan );
    vCone = Abc_MfxWinMarkTfi( pNode );

    // count the number of PIs
    nTrueSupp = 0;
    Vec_PtrForEachEntry( Nwk_Obj_t *, vCone, pObj, k )
        nTrueSupp += Nwk_ObjIsCi(pObj);
//    printf( "%d(%d) ", Vec_PtrSize(p->vSupp), m );

    // mark with the current trav ID those nodes that should not be divisors:
    // (1) the node and its TFO
    // (2) the MFFC of the node
    // (3) the node's fanins (these are treated as a special case)
    Nwk_ManIncrementTravId( pNode->pMan );
    Abc_MfxWinSweepLeafTfo_rec( pNode, tArrivalMax );
    Abc_MfxWinVisitMffc( pNode );
    Nwk_ObjForEachFanin( pNode, pObj, k )
        Nwk_ObjSetTravIdCurrent( pObj );

    // at this point the nodes are marked with two trav IDs:
    // nodes to be collected as divisors are marked with previous trav ID
    // nodes to be avoided as divisors are marked with current trav ID

    // start collecting the divisors
    vDivs = Vec_PtrAlloc( p->pPars->nDivMax );
    Vec_PtrForEachEntry( Nwk_Obj_t *, vCone, pObj, k )
    {
        if ( !Nwk_ObjIsTravIdPrevious(pObj) )
            continue;
        if ( Nwk_ObjArrival(pObj) > tArrivalMax )
            continue;
        Vec_PtrPush( vDivs, pObj );
        if ( Vec_PtrSize(vDivs) >= p->pPars->nDivMax )
            break;
    }
    Vec_PtrFree( vCone );

    // explore the fanouts of already collected divisors
    if ( Vec_PtrSize(vDivs) < p->pPars->nDivMax )
    Vec_PtrForEachEntry( Nwk_Obj_t *, vDivs, pObj, k )
    {
        // consider fanouts of this node
        Nwk_ObjForEachFanout( pObj, pFanout, f )
        {
            // stop if there are too many fanouts
            if ( f > 20 )
                break;
            // skip nodes that are already added
            if ( Nwk_ObjIsTravIdPrevious(pFanout) )
                continue;
            // skip nodes in the TFO or in the MFFC of node
            if ( Nwk_ObjIsTravIdCurrent(pFanout) )
                continue;
            // skip COs
            if ( !Nwk_ObjIsNode(pFanout) ) 
                continue;
            // skip nodes with large level
            if ( Nwk_ObjArrival(pFanout) > tArrivalMax )
                continue;
            // skip nodes whose fanins are not divisors
            Nwk_ObjForEachFanin( pFanout, pFanin, m )
                if ( !Nwk_ObjIsTravIdPrevious(pFanin) )
                    break;
            if ( m < Nwk_ObjFaninNum(pFanout) )
                continue;
            // make sure this divisor in not among the nodes
//            Vec_PtrForEachEntry( Aig_Obj_t *, p->vNodes, pFanin, m )
//                assert( pFanout != pFanin );
            // add the node to the divisors
            Vec_PtrPush( vDivs, pFanout );
//            Vec_PtrPush( p->vNodes, pFanout );
            Vec_PtrPushUnique( p->vNodes, pFanout );
            Nwk_ObjSetTravIdPrevious( pFanout );
            nDivsPlus++;
            if ( Vec_PtrSize(vDivs) >= p->pPars->nDivMax )
                break;
        }
        if ( Vec_PtrSize(vDivs) >= p->pPars->nDivMax )
            break;
    }

    // sort the divisors by level in the increasing order
    Vec_PtrSort( vDivs, (int (*)(void))Nwk_NodeCompareLevelsIncrease );

    // add the fanins of the node
    Nwk_ObjForEachFanin( pNode, pFanin, k )
        Vec_PtrPush( vDivs, pFanin );

/*
    printf( "Node level = %d.  ", Nwk_ObjLevel(p->pNode) );
    Vec_PtrForEachEntryStart( vDivs, pObj, k, Vec_PtrSize(vDivs)-p->nDivsPlus )
        printf( "%d ", Nwk_ObjLevel(pObj) );
    printf( "\n" );
*/
//printf( "%d ", p->nDivsPlus );
//    printf( "(%d+%d)(%d+%d+%d) ", Vec_PtrSize(p->vSupp), Vec_PtrSize(p->vNodes), 
//        nTrueSupp, Vec_PtrSize(vDivs)-nTrueSupp-nDivsPlus, nDivsPlus );
    return vDivs;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

