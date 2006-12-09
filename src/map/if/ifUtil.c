/**CFile****************************************************************

  FileName    [ifUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifUtil.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the max delay of the POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManDelayMax( If_Man_t * p )
{
    If_Obj_t * pObj;
    float DelayBest;
    int i;
    if ( p->pPars->fLatchPaths && p->pPars->nLatches == 0 )
    {
        printf( "Delay optimization of latch path is not performed because there is no latches.\n" );
        p->pPars->fLatchPaths = 0;
    }
    DelayBest = -IF_FLOAT_LARGE;
    if ( p->pPars->fLatchPaths )
    {
        If_ManForEachLatch( p, pObj, i )
            if ( DelayBest < If_ObjCutBest( If_ObjFanin0(pObj) )->Delay )
                 DelayBest = If_ObjCutBest( If_ObjFanin0(pObj) )->Delay;
    }
    else
    {
        If_ManForEachPo( p, pObj, i )
            if ( DelayBest < If_ObjCutBest( If_ObjFanin0(pObj) )->Delay )
                 DelayBest = If_ObjCutBest( If_ObjFanin0(pObj) )->Delay;
    }
    return DelayBest;
}

/**Function*************************************************************

  Synopsis    [Sets all the node copy to NULL.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManCleanNodeCopy( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
        If_ObjSetCopy( pObj, NULL );
}

/**Function*************************************************************

  Synopsis    [Sets all the cut data to NULL.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManCleanCutData( If_Man_t * p )
{
    If_Obj_t * pObj;
    If_Cut_t * pCut;
    int i, k;
    If_ManForEachObj( p, pObj, i )
        If_ObjForEachCut( pObj, pCut, k )
            If_CutSetData( pCut, NULL );
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMapping_rec( If_Man_t * p, If_Obj_t * pObj, If_Obj_t ** ppStore )
{
    If_Obj_t * pLeaf;
    If_Cut_t * pCutBest;
    float aArea;
    int i;
    if ( pObj->nRefs++ || If_ObjIsPi(pObj) || If_ObjIsConst1(pObj) )
        return 0.0;
    // store the node in the structure by level
    assert( If_ObjIsAnd(pObj) );
    pObj->pCopy = (char *)ppStore[pObj->Level]; 
    ppStore[pObj->Level] = pObj;
    // visit the transitive fanin of the selected cut
    pCutBest = If_ObjCutBest(pObj);
    aArea = If_CutLutArea( p, pCutBest );
    If_CutForEachLeaf( p, pCutBest, pLeaf, i )
        aArea += If_ManScanMapping_rec( p, pLeaf, ppStore );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMapping( If_Man_t * p )
{
    If_Obj_t * pObj, ** ppStore;
    float aArea;
    int i;
    // clean all references
    If_ManForEachObj( p, pObj, i )
    {
        pObj->Required = IF_FLOAT_LARGE;
        pObj->nRefs = 0;
    }
    // allocate place to store the nodes
    ppStore = ALLOC( If_Obj_t *, p->nLevelMax + 1 );
    memset( ppStore, 0, sizeof(If_Obj_t *) * (p->nLevelMax + 1) );
    // collect nodes reachable from POs in the DFS order through the best cuts
    aArea = 0;
    If_ManForEachPo( p, pObj, i )
        aArea += If_ManScanMapping_rec( p, If_ObjFanin0(pObj), ppStore );
    // reconnect the nodes in reverse topological order
    Vec_PtrClear( p->vMapped );
    for ( i = p->nLevelMax; i >= 0; i-- )
        for ( pObj = ppStore[i]; pObj; pObj = pObj->pCopy )
            Vec_PtrPush( p->vMapped, pObj );
    free( ppStore );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes the required times of all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManComputeRequired( If_Man_t * p, int fFirstTime )
{
    If_Obj_t * pObj;
    int i;
    // compute area, clean required times, collect nodes used in the mapping
    p->AreaGlo = If_ManScanMapping( p );
    // get the global required times
    p->RequiredGlo = If_ManDelayMax( p );
    // update the required times according to the target
    if ( p->pPars->DelayTarget != -1 )
    {
        if ( p->RequiredGlo > p->pPars->DelayTarget + p->fEpsilon )
        {
            if ( fFirstTime )
                printf( "Cannot meet the target required times (%4.2f). Mapping continues anyway.\n", p->pPars->DelayTarget );
        }
        else if ( p->RequiredGlo < p->pPars->DelayTarget - p->fEpsilon )
        {
            if ( fFirstTime )
                printf( "Relaxing the required times from (%4.2f) to the target (%4.2f).\n", p->RequiredGlo, p->pPars->DelayTarget );
            p->RequiredGlo = p->pPars->DelayTarget;
        }
    }
    // set the required times for the POs
    if ( p->pPars->fLatchPaths )
    {
        If_ManForEachLatch( p, pObj, i )
            If_ObjFanin0(pObj)->Required = p->RequiredGlo;
    }
    else
    {
        If_ManForEachPo( p, pObj, i )
            If_ObjFanin0(pObj)->Required = p->RequiredGlo;
    }
    // go through the nodes in the reverse topological order
    Vec_PtrForEachEntry( p->vMapped, pObj, i )
        If_CutPropagateRequired( p, If_ObjCutBest(pObj), pObj->Required );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


