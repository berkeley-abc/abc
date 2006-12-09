/**CFile****************************************************************

  FileName    [ifCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifCut.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is contained in pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutCheckDominance( If_Cut_t * pDom, If_Cut_t * pCut )
{
    int i, k;
    for ( i = 0; i < (int)pDom->nLeaves; i++ )
    {
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
            if ( pDom->pLeaves[i] == pCut->pLeaves[k] )
                break;
        if ( k == (int)pCut->nLeaves ) // node i in pDom is not contained in pCut
            return 0;
    }
    // every node in pDom is contained in pCut
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is equal to pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutCheckEquality( If_Cut_t * pDom, If_Cut_t * pCut )
{
    int i;
    if ( (int)pDom->nLeaves != (int)pCut->nLeaves )
        return 0;
    for ( i = 0; i < (int)pDom->nLeaves; i++ )
        if ( pDom->pLeaves[i] != pCut->pLeaves[i] )
            return 0;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Returns 1 if the cut is contained.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutFilter( If_Man_t * p, If_Cut_t * pCut )
{
    If_Cut_t * pTemp;
    int i;
    for ( i = 0; i < p->nCuts; i++ )
    {
        pTemp = p->ppCuts[i];
        if ( pTemp->nLeaves > pCut->nLeaves )
        {
            // do not fiter the first cut
            if ( i == 0 )
                continue;
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pCut->uSign )
                continue;
            // check containment seriously
            if ( If_CutCheckDominance( pCut, pTemp ) )
            {
                // removed contained cut
                p->ppCuts[i] = p->ppCuts[p->nCuts-1];
                p->ppCuts[p->nCuts-1] = pTemp;
                p->nCuts--;
                i--;
            }
         }
        else
        {
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pTemp->uSign )
                continue;
            // check containment seriously
            if ( If_CutCheckDominance( pTemp, pCut ) )
                return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Merges two cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutMergeOrdered( If_Cut_t * pC0, If_Cut_t * pC1, If_Cut_t * pC )
{ 
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );
    // the case of the largest cut sizes
    if ( pC0->nLeaves == pC->nLimit && pC1->nLeaves == pC->nLimit )
    {
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            if ( pC0->pLeaves[i] != pC1->pLeaves[i] )
                return 0;
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }
    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == pC->nLimit )
    {
        for ( i = 0; i < (int)pC1->nLeaves; i++ )
        {
            for ( k = (int)pC0->nLeaves - 1; k >= 0; k-- )
                if ( pC0->pLeaves[k] == pC1->pLeaves[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < (int)pC->nLimit; c++ )
    {
        if ( k == (int)pC1->nLeaves )
        {
            if ( i == (int)pC0->nLeaves )
            {
                pC->nLeaves = c;
                return 1;
            }
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( i == (int)pC0->nLeaves )
        {
            if ( k == (int)pC1->nLeaves )
            {
                pC->nLeaves = c;
                return 1;
            }
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        if ( pC0->pLeaves[i] < pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( pC0->pLeaves[i] > pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        pC->pLeaves[c] = pC0->pLeaves[i++]; 
        k++;
    }
    if ( i < (int)pC0->nLeaves || k < (int)pC1->nLeaves )
        return 0;
    pC->nLeaves = c;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Merges two cuts.]

  Description [Special case when the cut is known to exist.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutMergeOrdered2( If_Cut_t * pC0, If_Cut_t * pC1, If_Cut_t * pC )
{ 
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );
    // copy the first cut
    for ( i = 0; i < (int)pC0->nLeaves; i++ )
        pC->pLeaves[i] = pC0->pLeaves[i];
    pC->nLeaves = pC0->nLeaves;
    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == pC->nLimit )
        return 1;
    // add nodes of the second cut
    k = 0;
    for ( i = 0; i < (int)pC1->nLeaves; i++ )
    {
        // find k-th node before which i-th node should be added
        for ( ; k < (int)pC->nLeaves; k++ )
            if ( pC->pLeaves[k] >= pC1->pLeaves[i] )
                break;
        // check the case when this should be the last node
        if ( k == (int)pC->nLeaves )
        {
            pC->pLeaves[k++] = pC1->pLeaves[i];
            pC->nLeaves++;
            continue;
        }
        // check the case when equal node is found
        if ( pC1->pLeaves[i] == pC->pLeaves[k] )
            continue;
        // add the node
        for ( c = (int)pC->nLeaves; c > k; c-- )
            pC->pLeaves[c] = pC->pLeaves[c-1];
        pC->pLeaves[k++] = pC1->pLeaves[i];
        pC->nLeaves++;
    }
    assert( pC->nLeaves <= pC->nLimit );
    for ( i = 1; i < (int)pC->nLeaves; i++ )
        assert( pC->pLeaves[i-1] < pC->pLeaves[i] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutMerge( If_Cut_t * pCut0, If_Cut_t * pCut1, If_Cut_t * pCut )
{ 
    assert( pCut->nLimit > 0 );
    // merge the nodes
    if ( pCut0->nLeaves < pCut1->nLeaves )
    {
        if ( !If_CutMergeOrdered( pCut1, pCut0, pCut ) )
            return 0;
    }
    else
    {
        if ( !If_CutMergeOrdered( pCut0, pCut1, pCut ) )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutCompareDelay( If_Cut_t ** ppC0, If_Cut_t ** ppC1 )
{
    If_Cut_t * pC0 = *ppC0;
    If_Cut_t * pC1 = *ppC1;
    if ( pC0->Delay < pC1->Delay - 0.0001 )
        return -1;
    if ( pC0->Delay > pC1->Delay + 0.0001 )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    if ( pC0->Area < pC1->Area - 0.0001 )
        return -1;
    if ( pC0->Area > pC1->Area + 0.0001 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutCompareDelayOld( If_Cut_t ** ppC0, If_Cut_t ** ppC1 )
{
    If_Cut_t * pC0 = *ppC0;
    If_Cut_t * pC1 = *ppC1;
    if ( pC0->Delay < pC1->Delay - 0.0001 )
        return -1;
    if ( pC0->Delay > pC1->Delay + 0.0001 )
        return 1;
    if ( pC0->Area < pC1->Area - 0.0001 )
        return -1;
    if ( pC0->Area > pC1->Area + 0.0001 )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutCompareArea( If_Cut_t ** ppC0, If_Cut_t ** ppC1 )
{
    If_Cut_t * pC0 = *ppC0;
    If_Cut_t * pC1 = *ppC1;
    if ( pC0->Area < pC1->Area - 0.0001 )
        return -1;
    if ( pC0->Area > pC1->Area + 0.0001 )
        return 1;
    if ( pC0->AveRefs > pC1->AveRefs )
        return -1;
    if ( pC0->AveRefs < pC1->AveRefs )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    if ( pC0->Delay < pC1->Delay - 0.0001 )
        return -1;
    if ( pC0->Delay > pC1->Delay + 0.0001 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sorts the cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManSortCuts( If_Man_t * p, int Mode )
{
    // sort the cuts
    if ( Mode || p->pPars->fArea ) // area
        qsort( p->ppCuts, p->nCuts, sizeof(If_Cut_t *), (int (*)(const void *, const void *))If_CutCompareArea );
    else if ( p->pPars->fFancy )
        qsort( p->ppCuts, p->nCuts, sizeof(If_Cut_t *), (int (*)(const void *, const void *))If_CutCompareDelayOld );
    else
        qsort( p->ppCuts, p->nCuts, sizeof(If_Cut_t *), (int (*)(const void *, const void *))If_CutCompareDelay );
}

/**Function*************************************************************

  Synopsis    [Computes area flow.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutFlow( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    float Flow;
    int i;
    assert( pCut->nLeaves > 1 );
    Flow = If_CutLutArea(p, pCut);
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        if ( pLeaf->nRefs == 0 )
            Flow += If_ObjCutBest(pLeaf)->Area;
        else
        {
            assert( pLeaf->EstRefs > p->fEpsilon );
            Flow += If_ObjCutBest(pLeaf)->Area / pLeaf->EstRefs;
        }
    }
    return Flow;
}

/**Function*************************************************************

  Synopsis    [Average number of references of the leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutAverageRefs( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    int nRefsTotal, i;
    assert( pCut->nLeaves > 1 );
    nRefsTotal = 0;
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        nRefsTotal += pLeaf->nRefs;
    return ((float)nRefsTotal)/pCut->nLeaves;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutDeref( If_Man_t * p, If_Cut_t * pCut, int nLevels )
{
    If_Obj_t * pLeaf;
    float Area;
    int i;
    Area = If_CutLutArea(p, pCut);
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs > 0 );
        if ( --pLeaf->nRefs > 0 || !If_ObjIsAnd(pLeaf) || nLevels == 1 )
            continue;
        Area += If_CutDeref( p, If_ObjCutBest(pLeaf), nLevels - 1 );
    }
    return Area;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutRef( If_Man_t * p, If_Cut_t * pCut, int nLevels )
{
    If_Obj_t * pLeaf;
    float Area;
    int i;
    Area = If_CutLutArea(p, pCut);
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs >= 0 );
        if ( pLeaf->nRefs++ > 0 || !If_ObjIsAnd(pLeaf) || nLevels == 1 )
            continue;
        Area += If_CutRef( p, If_ObjCutBest(pLeaf), nLevels - 1 );
    }
    return Area;
}

/**Function*************************************************************

  Synopsis    [Prints one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutPrint( If_Man_t * p, If_Cut_t * pCut )
{
    unsigned i;
    printf( "{" );
    for ( i = 0; i < pCut->nLeaves; i++ )
        printf( " %d", pCut->pLeaves[i] );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    [Prints one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutPrintTiming( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    unsigned i;
    printf( "{" );
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        printf( " %d(%.2f/%.2f)", pLeaf->Id, If_ObjCutBest(pLeaf)->Delay, pLeaf->Required );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutAreaDerefed( If_Man_t * p, If_Cut_t * pCut, int nLevels )
{
    float aResult, aResult2;
    assert( pCut->nLeaves > 1 );
    aResult2 = If_CutRef( p, pCut, nLevels );
    aResult  = If_CutDeref( p, pCut, nLevels );
    assert( aResult == aResult2 );
    return aResult;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutAreaRefed( If_Man_t * p, If_Cut_t * pCut, int nLevels )
{
    float aResult, aResult2;
    assert( pCut->nLeaves > 1 );
    aResult2 = If_CutDeref( p, pCut, nLevels );
    aResult  = If_CutRef( p, pCut, nLevels );
    assert( aResult == aResult2 );
    return aResult;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutCopy( If_Cut_t * pCutDest, If_Cut_t * pCutSrc )
{
    int * pLeaves;
    char * pPerm;
    unsigned * pTruth;
    // save old arrays
    pLeaves = pCutDest->pLeaves;
    pPerm   = pCutDest->pPerm;
    pTruth  = pCutDest->pTruth;
    // copy the cut info
    *pCutDest = *pCutSrc;
    // restore the arrays
    pCutDest->pLeaves = pLeaves;
    pCutDest->pPerm   = pPerm;
    pCutDest->pTruth  = pTruth;
    // copy the array data
    memcpy( pCutDest->pLeaves, pCutSrc->pLeaves, sizeof(int) * pCutSrc->nLeaves );
    if ( pCutSrc->pPerm )
        memcpy( pCutDest->pPerm, pCutSrc->pPerm, sizeof(unsigned) * If_CutPermWords(pCutSrc->nLimit) );
    if ( pCutSrc->pTruth )
        memcpy( pCutDest->pTruth, pCutSrc->pTruth, sizeof(unsigned) * If_CutTruthWords(pCutSrc->nLimit) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


