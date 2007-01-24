/**CFile****************************************************************

  FileName    [resDivs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Collect divisors for the given window.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resDivs.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "resInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds candidate divisors of the node to its window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinDivisors( Res_Win_t * p, int nLevDivMax )
{
    Abc_Obj_t * pObj, * pFanout, * pFanin;
    int i, k, f, m;

    p->nLevDivMax = nLevDivMax;

    // mark the leaves and the internal nodes
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 1;
    Vec_VecForEachEntry( p->vLevels, pObj, i, k )
        pObj->fMarkA = 1;

    // prepare the new trav ID
    Abc_NtkIncrementTravId( p->pNode->pNtk );
    // mark the TFO of the node (does not increment trav ID)
    Res_WinSweepLeafTfo_rec( p->pNode, p->nLevDivMax, NULL );
    // mark the MFFC of the node (does not increment trav ID)
    Res_WinVisitMffc( p );

    // go through all the legal levels and check if their fanouts can be divisors
    p->nDivsPlus = 0;
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevDivMax - 1 )
    {
        // skip nodes in the TFO or in the MFFC of node
        if ( Abc_NodeIsTravIdCurrent(pObj) )
            continue;
        // consider fanouts of this node
        Abc_ObjForEachFanout( pObj, pFanout, f )
        {
            // skip nodes that are already added
            if ( pFanout->fMarkA )
                continue;
            // skip COs
            if ( !Abc_ObjIsNode(pFanout) ) 
                continue;
            // skip nodes in the TFO or in the MFFC of node
            if ( Abc_NodeIsTravIdCurrent(pFanout) )
                continue;
            // skip nodes with large level
            if ( (int)pFanout->Level > p->nLevDivMax )
                continue;
            // skip nodes whose fanins are not in the cone
            Abc_ObjForEachFanin( pFanout, pFanin, m )
                if ( !pFanin->fMarkA )
                    break;
            if ( m < Abc_ObjFaninNum(pFanout) )
                continue;
            // add the node
            Res_WinAddNode( p, pFanout );
            p->nDivsPlus++;
        }
    }

    // unmark the leaves and the internal nodes
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 0;
    Vec_VecForEachEntry( p->vLevels, pObj, i, k )
        pObj->fMarkA = 0;

    // collect the divisors below the line
    Vec_PtrClear( p->vDivs );
    // collect the node fanins first and mark the fanins
    Abc_ObjForEachFanin( p->pNode, pFanin, m )
    {
        Vec_PtrPush( p->vDivs, pFanin );
        Abc_NodeSetTravIdCurrent( pFanin );
    }
    // collect the remaining leaves
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        if ( !Abc_NodeIsTravIdCurrent(pObj) )
            Vec_PtrPush( p->vDivs, pObj );
    // collect remaining unvisited divisors 
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, p->nLevLeaves, p->nLevDivMax )
        if ( !Abc_NodeIsTravIdCurrent(pObj) )
            Vec_PtrPush( p->vDivs, pObj );

    // verify the resulting window
//    Res_WinVerify( p );
}

/**Function*************************************************************

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_NodeDeref_rec( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    Abc_NodeSetTravIdCurrent( pNode );
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        assert( pFanin->vFanouts.nSize > 0 );
        if ( --pFanin->vFanouts.nSize == 0 )
            Counter += Res_NodeDeref_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_NodeRef_rec( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i, Counter = 1;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( pFanin->vFanouts.nSize++ == 0 )
            Counter += Res_NodeRef_rec( pFanin );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Labels MFFC of the node with the current trav ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_WinVisitMffc( Res_Win_t * p )
{
    int Count1, Count2;
    // dereference the node (mark with the current trav ID)
    Count1 = Res_NodeDeref_rec( p->pNode );
    // reference it back
    Count2 = Res_NodeRef_rec( p->pNode );
    assert( Count1 == Count2 );
    return Count1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


