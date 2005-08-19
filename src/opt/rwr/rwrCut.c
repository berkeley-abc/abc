/**CFile****************************************************************

  FileName    [rwrCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrCut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Rwr_Cut_t * Rwr_CutAlloc( Rwr_Man_t * p );
static Rwr_Cut_t * Rwr_CutCreateTriv( Rwr_Man_t * p, Abc_Obj_t * pNode );
static Rwr_Cut_t * Rwr_CutsMerge( Rwr_Man_t * p, Rwr_Cut_t * pCut0, Rwr_Cut_t * pCut1, int fCompl0, int fCompl1 );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes cuts for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_NtkStartCuts( Rwr_Man_t * p, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    // set the trivial cuts
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)Rwr_CutCreateTriv( p, pNode );
}

/**Function*************************************************************

  Synopsis    [Computes cuts for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_NodeComputeCuts( Rwr_Man_t * p, Abc_Obj_t * pNode )
{
    Rwr_Cut_t * pCuts0, * pCuts1, * pTemp0, * pTemp1, * pCut;
    Rwr_Cut_t * pList = NULL, ** ppPlace = &pList; // linked list of cuts
    assert( Abc_ObjIsNode(pNode) );
    if ( Abc_NodeIsConst(pNode) )
        return;
    // create the elementary cut
    pCut = Rwr_CutCreateTriv( p, pNode );
    // add it to the linked list
    *ppPlace = pCut;  ppPlace  = &pCut->pNext;
    // create cuts by merging pairwise
    pCuts0 = (Rwr_Cut_t *)Abc_ObjFanin0(pNode)->pCopy;
    pCuts1 = (Rwr_Cut_t *)Abc_ObjFanin1(pNode)->pCopy;
    assert( pCuts0 && pCuts1 );
    for ( pTemp0 = pCuts0; pTemp0; pTemp0 = pTemp0->pNext )
    for ( pTemp1 = pCuts1; pTemp1; pTemp1 = pTemp1->pNext )
    {
        pCut = Rwr_CutsMerge( p, pTemp0, pTemp1, Abc_ObjFaninC0(pNode), Abc_ObjFaninC1(pNode) );
        if ( pCut == NULL )
            continue;
        // add it to the linked list
        *ppPlace = pCut;  ppPlace  = &pCut->pNext;
    }
    // set the linked list
    pNode->pCopy = (Abc_Obj_t *)pList;
}

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Cut_t * Rwr_CutsMerge( Rwr_Man_t * p, Rwr_Cut_t * pCut0, Rwr_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    Abc_Obj_t * ppNodes[4], * pNodeTemp;
    Rwr_Cut_t * pCut;
    unsigned uPhase, uTruth0, uTruth1;
    int i, k, min, nTotal;

    // solve the most typical case: both cuts are four input
    if ( pCut0->nLeaves == 4 && pCut1->nLeaves == 4 )
    {
        for ( i = 0; i < 4; i++ )
            if ( pCut0->ppLeaves[i] != pCut1->ppLeaves[i] )
                return NULL;
        // create the cut
        pCut = Rwr_CutAlloc( p );
        pCut->nLeaves = 4;
        for ( i = 0; i < 4; i++ )
            pCut->ppLeaves[i] = pCut0->ppLeaves[i];
        pCut->uTruth = (fCompl0? ~pCut0->uTruth : pCut0->uTruth) & (fCompl1? ~pCut1->uTruth : pCut1->uTruth) & 0xFFFF;
        return pCut;
    }

    // create the set of new nodes
    // count the number of unique entries in pCut1
    nTotal = pCut0->nLeaves;
    for ( i = 0; i < (int)pCut1->nLeaves; i++ )
    {
        // try to find this entry among the leaves of pCut0
        for ( k = 0; k < (int)pCut0->nLeaves; k++ )
            if ( pCut1->ppLeaves[i] == pCut0->ppLeaves[k] )
                break;
        if ( k < (int)pCut0->nLeaves ) // found
            continue;
        // we found a new entry to add
        if ( nTotal == 4 )
            return NULL;
        ppNodes[nTotal++] = pCut1->ppLeaves[i];
    }
    // we know that the feasible cut exists

    // add the starting entries
    for ( k = 0; k < (int)pCut0->nLeaves; k++ )
        ppNodes[k] = pCut0->ppLeaves[k];

    // selection-sort the entries
    for ( i = 0; i < nTotal - 1; i++ )
    {
        min = i;
        for ( k = i+1; k < nTotal; k++ )
            if ( ppNodes[k]->Id < ppNodes[min]->Id )
                min = k;
        pNodeTemp    = ppNodes[i];
        ppNodes[i]   = ppNodes[min];
        ppNodes[min] = pNodeTemp;
    }

    // find the mapping from the old nodes to the new
    if ( pCut0->nLeaves == 4 )
        uTruth0 = pCut0->uTruth;
    else
    {
        uPhase = 0;
        for ( i = 0; i < (int)pCut0->nLeaves; i++ )
        {
            for ( k = 0; k < nTotal; k++ )
                if ( pCut0->ppLeaves[i] == ppNodes[k] )
                    break;
            uPhase |= (1 << k);
        }
        assert( uPhase < 16 );
        assert( pCut0->uTruth < 256 );
        uTruth0 = p->puPerms43[pCut0->uTruth][uPhase];
    }

    // find the mapping from the old nodes to the new
    if ( pCut1->nLeaves == 4 )
        uTruth1 = pCut1->uTruth;
    else
    {
        uPhase = 0;
        for ( i = 0; i < (int)pCut1->nLeaves; i++ )
        {
            for ( k = 0; k < nTotal; k++ )
                if ( pCut1->ppLeaves[i] == ppNodes[k] )
                    break;
            uPhase |= (1 << k);
        }
        assert( uPhase < 16 );
        assert( pCut1->uTruth < 256 );
        uTruth1 = p->puPerms43[pCut1->uTruth][uPhase];
    }

    // create the cut
    pCut = Rwr_CutAlloc( p );
    pCut->nLeaves = nTotal;
    for ( i = 0; i < nTotal; i++ )
        pCut->ppLeaves[i] = ppNodes[i];
    pCut->uTruth = (fCompl0? ~uTruth0 : uTruth0) & (fCompl1? ~uTruth1 : uTruth1) & 0xFFFF;
    return pCut;
}

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Cut_t * Rwr_CutAlloc( Rwr_Man_t * p )
{
    Rwr_Cut_t * pCut;
    pCut = (Rwr_Cut_t *)Extra_MmFixedEntryFetch( p->pMmNode );
    memset( pCut, 0, sizeof(Rwr_Cut_t) );
    return pCut;
}

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Cut_t * Rwr_CutCreateTriv( Rwr_Man_t * p, Abc_Obj_t * pNode )
{
    Rwr_Cut_t * pCut;
    pCut = Rwr_CutAlloc( p );
    pCut->nLeaves = 1;
    pCut->ppLeaves[0] = pNode;
    pCut->uTruth = 0xAAAA;
    return pCut;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


