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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#if 0

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Aig_CutDeref( Aig_Man_t * p, Dar_Cut_t * pCut )
{ 
    Aig_Obj_t * pLeaf;
    int i;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs > 0 );
        if ( --pLeaf->nRefs > 0 || !Aig_ObjIsAnd(pLeaf) )
            continue;
        Aig_CutDeref( p, Aig_ObjBestCut(pLeaf) );
    }
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_CutRef( Aig_Man_t * p, Dar_Cut_t * pCut )
{
    Aig_Obj_t * pLeaf;
    int i, Area = pCut->Value;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs >= 0 );
        if ( pLeaf->nRefs++ > 0 || !Aig_ObjIsAnd(pLeaf) )
            continue;
        Area += Aig_CutRef( p, Aig_ObjBestCut(pLeaf) );
    }
    return Area;
}

/**Function*************************************************************

  Synopsis    [Computes exact area of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_CutArea( Aig_Man_t * p, Dar_Cut_t * pCut )
{
    int Area;
    Area = Aig_CutRef( p, pCut );
    Aig_CutDeref( p, pCut );
    return Area;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the second cut is better.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cnf_CutCompare( Dar_Cut_t * pC0, Dar_Cut_t * pC1 )
{
    if ( pC0->Area < pC1->Area - 0.0001 )
        return -1;
    if ( pC0->Area > pC1->Area + 0.0001 ) // smaller area flow is better
        return 1;
//    if ( pC0->NoRefs < pC1->NoRefs )
//        return -1;
//    if ( pC0->NoRefs > pC1->NoRefs ) // fewer non-referenced fanins is better
//        return 1;
//    if ( pC0->FanRefs / pC0->nLeaves > pC1->FanRefs / pC1->nLeaves )
//        return -1;
//    if ( pC0->FanRefs / pC0->nLeaves < pC1->FanRefs / pC1->nLeaves )
//        return 1; // larger average fanin ref-counter is better
//    return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the cut with the smallest area flow.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cut_t * Cnf_ObjFindBestCut( Aig_Obj_t * pObj )
{
    Dar_Cut_t * pCut, * pCutBest;
    int i;
    pCutBest = NULL;
    Dar_ObjForEachCut( pObj, pCut, i )
        if ( pCutBest == NULL || Cnf_CutCompare(pCutBest, pCut) == 1 )
            pCutBest = pCut;
    return pCutBest;
}

/**Function*************************************************************

  Synopsis    [Computes area flow of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CutAssignAreaFlow( Cnf_Man_t * p, Dar_Cut_t * pCut )
{
    Aig_Obj_t * pLeaf;
    int i;
    pCut->Cost    = p->pSopSizes[pCut->uTruth] + p->pSopSizes[0xFFFF & ~pCut->uTruth];
    pCut->Area    = (float)pCut->Cost;
    pCut->NoRefs  = 0;
    pCut->FanRefs = 0;
    Dar_CutForEachLeaf( p->pManAig, pCut, pLeaf, i )
    {
        if ( !Aig_ObjIsNode(pLeaf) )
            continue;
        if ( pLeaf->nRefs == 0 )
        {
            pCut->Area += Aig_ObjBestCut(pLeaf)->Area;
            pCut->NoRefs++;
        }
        else
        {
            pCut->Area += Aig_ObjBestCut(pLeaf)->Area / pLeaf->nRefs;
            if ( pCut->FanRefs + pLeaf->nRefs > 15 )
                pCut->FanRefs = 15;
            else
                pCut->FanRefs += pLeaf->nRefs;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Computes area flow of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CutAssignArea( Cnf_Man_t * p, Dar_Cut_t * pCut )
{
    Aig_Obj_t * pLeaf;
    int i;
    pCut->Area    = (float)pCut->Cost;
    pCut->NoRefs  = 0;
    pCut->FanRefs = 0;
    Dar_CutForEachLeaf( p->pManAig, pCut, pLeaf, i )
    {
        if ( !Aig_ObjIsNode(pLeaf) )
            continue;
        if ( pLeaf->nRefs == 0 )
        {
            pCut->Area += Aig_ObjBestCut(pLeaf)->Cost;
            pCut->NoRefs++;
        }
        else
        {
            if ( pCut->FanRefs + pLeaf->nRefs > 15 )
                pCut->FanRefs = 15;
            else
                pCut->FanRefs += pLeaf->nRefs;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs one round of "area recovery" using exact local area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_ManMapForCnf( Cnf_Man_t * p )
{
    Aig_Obj_t * pObj;
    Dar_Cut_t * pCut, * pCutBest;
    int i, k;
    // visit the nodes in the topological order and update their best cuts
    Aig_ManForEachNode( p->pManAig, pObj, i )
    {
        // find the old best cut
        pCutBest = Aig_ObjBestCut(pObj);
        Dar_ObjClearBestCut(pCutBest);
        // if the node is used, dereference its cut
        if ( pObj->nRefs )
            Aig_CutDeref( p->pManAig, pCutBest );

        // evaluate the cuts of this node
        Dar_ObjForEachCut( pObj, pCut, k )
//            Cnf_CutAssignAreaFlow( p, pCut );
            pCut->Area = (float)Cnf_CutArea( p->pManAig, pCut );

        // find the new best cut
        pCutBest = Cnf_ObjFindBestCut(pObj);
        Dar_ObjSetBestCut( pCutBest );
        // if the node is used, reference its cut
        if ( pObj->nRefs )
            Aig_CutRef( p->pManAig, pCutBest );
    }
    return 1;
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


