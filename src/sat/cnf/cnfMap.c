/**CFile****************************************************************

  FileName    [cnfMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG-to-CNF conversion.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: cnfMap.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cnf.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes area flow of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CutAssignAreaFlow( Cnf_Man_t * p, Dar_Cut_t * pCut, int * pAreaFlows )
{
    Aig_Obj_t * pLeaf;
    int i;
    pCut->Value = 0;
//    pCut->uSign = 100 * Cnf_CutSopCost( p, pCut );
    pCut->uSign = 10 * Cnf_CutSopCost( p, pCut );
    Dar_CutForEachLeaf( p->pManAig, pCut, pLeaf, i )
    {
        pCut->Value += pLeaf->nRefs;
        if ( !Aig_ObjIsNode(pLeaf) )
            continue;
        assert( pLeaf->nRefs > 0 );
        pCut->uSign += pAreaFlows[pLeaf->Id] / (pLeaf->nRefs? pLeaf->nRefs : 1);
    }
}

/**Function*************************************************************

  Synopsis    [Computes area flow of the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_CutSuperAreaFlow( Vec_Ptr_t * vSuper, int * pAreaFlows )
{
    Aig_Obj_t * pLeaf;
    int i, nAreaFlow;
    nAreaFlow = 100 * (Vec_PtrSize(vSuper) + 1);
    Vec_PtrForEachEntry( Aig_Obj_t *, vSuper, pLeaf, i )
    {
        pLeaf = Aig_Regular(pLeaf);
        if ( !Aig_ObjIsNode(pLeaf) )
            continue;
        assert( pLeaf->nRefs > 0 );
        nAreaFlow += pAreaFlows[pLeaf->Id] / (pLeaf->nRefs? pLeaf->nRefs : 1);
    }
    return nAreaFlow;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DeriveMapping( Cnf_Man_t * p )
{
    Vec_Ptr_t * vSuper;
    Aig_Obj_t * pObj;
    Dar_Cut_t * pCut, * pCutBest;
    int i, k, AreaFlow, * pAreaFlows;
    // allocate area flows
    pAreaFlows = ABC_ALLOC( int, Aig_ManObjNumMax(p->pManAig) );
    memset( pAreaFlows, 0, sizeof(int) * Aig_ManObjNumMax(p->pManAig) );
    // visit the nodes in the topological order and update their best cuts
    vSuper = Vec_PtrAlloc( 100 );
    Aig_ManForEachNode( p->pManAig, pObj, i )
    {
        // go through the cuts
        pCutBest = NULL;
        Dar_ObjForEachCut( pObj, pCut, k )
        {
            pCut->fBest = 0;
            if ( k == 0 )
                continue;
            Cnf_CutAssignAreaFlow( p, pCut, pAreaFlows );
            if ( pCutBest == NULL || pCutBest->uSign > pCut->uSign || 
                (pCutBest->uSign == pCut->uSign && pCutBest->Value < pCut->Value) )
                 pCutBest = pCut;
        }
        // check the big cut
//        Aig_ObjCollectSuper( pObj, vSuper );
        // get the area flow of this cut
//        AreaFlow = Cnf_CutSuperAreaFlow( vSuper, pAreaFlows );
        AreaFlow = ABC_INFINITY;
        if ( AreaFlow >= (int)pCutBest->uSign )
        {
            pAreaFlows[pObj->Id] = pCutBest->uSign;
            pCutBest->fBest = 1;
        }
        else
        {
            pAreaFlows[pObj->Id] = AreaFlow;
            pObj->fMarkB = 1; // mark the special node
        }
    }
    Vec_PtrFree( vSuper );
    ABC_FREE( pAreaFlows );

/*
    // compute the area of mapping
    AreaFlow = 0;
    Aig_ManForEachCo( p->pManAig, pObj, i )
        AreaFlow += Dar_ObjBestCut(Aig_ObjFanin0(pObj))->uSign / 100 / Aig_ObjFanin0(pObj)->nRefs;
    printf( "Area of the network = %d.\n", AreaFlow );
*/
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

