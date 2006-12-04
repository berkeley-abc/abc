/**CFile****************************************************************

  FileName    [ifMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Mapping procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifMap.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
  Ideas to try:
  - reverse order of area recovery
  - ordering of the outputs by size
  - merging Delay, Delay2, and Area
  - expand/reduce area recovery

*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in the signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}

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
int If_CutFilter( If_Man_t * p, If_Cut_t * pCut, int Mode )
{
    If_Cut_t * pTemp;
    int i;
    for ( i = 0; i < p->nCuts; i++ )
    {
        pTemp = p->ppCuts[i];
        if ( pTemp->nLeaves > pCut->nLeaves )
        {
//            continue;
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
static inline int If_CutMergeOrdered( If_Cut_t * pC0, If_Cut_t * pC1, If_Cut_t * pC, int nLimit )
{ 
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );
    // the case of the largest cut sizes
    if ( pC0->nLeaves == nLimit && pC1->nLeaves == nLimit )
    {
        for ( i = 0; i < pC0->nLeaves; i++ )
            if ( pC0->pLeaves[i] != pC1->pLeaves[i] )
                return 0;
        for ( i = 0; i < pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }
    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == nLimit )
    {
        for ( i = 0; i < pC1->nLeaves; i++ )
        {
            for ( k = pC0->nLeaves - 1; k >= 0; k-- )
                if ( pC0->pLeaves[k] == pC1->pLeaves[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < nLimit; c++ )
    {
        if ( k == pC1->nLeaves )
        {
            if ( i == pC0->nLeaves )
            {
                pC->nLeaves = c;
                return 1;
            }
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( i == pC0->nLeaves )
        {
            if ( k == pC1->nLeaves )
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
    if ( i < pC0->nLeaves || k < pC1->nLeaves )
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
static inline int If_CutMergeOrdered2( If_Cut_t * pC0, If_Cut_t * pC1, If_Cut_t * pC, int nLimit )
{ 
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );
    // copy the first cut
    for ( i = 0; i < pC0->nLeaves; i++ )
        pC->pLeaves[i] = pC0->pLeaves[i];
    pC->nLeaves = pC0->nLeaves;
    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == nLimit )
        return 1;
    // add nodes of the second cut
    k = 0;
    for ( i = 0; i < pC1->nLeaves; i++ )
    {
        // find k-th node before which i-th node should be added
        for ( ; k < pC->nLeaves; k++ )
            if ( pC->pLeaves[k] >= pC1->pLeaves[i] )
                break;
        // check the case when this should be the last node
        if ( k == pC->nLeaves )
        {
            pC->pLeaves[k++] = pC1->pLeaves[i];
            pC->nLeaves++;
            continue;
        }
        // check the case when equal node is found
        if ( pC1->pLeaves[i] == pC->pLeaves[k] )
            continue;
        // add the node
        for ( c = pC->nLeaves; c > k; c-- )
            pC->pLeaves[c] = pC->pLeaves[c-1];
        pC->pLeaves[k++] = pC1->pLeaves[i];
        pC->nLeaves++;
    }
    assert( pC->nLeaves <= nLimit );
    for ( i = 1; i < pC->nLeaves; i++ )
        assert( pC->pLeaves[i-1] < pC->pLeaves[i] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutMerge( If_Cut_t * pCut0, If_Cut_t * pCut1, If_Cut_t * pCut, int nLimit )
{ 
    // merge the nodes
    if ( pCut0->nLeaves < pCut1->nLeaves )
    {
        if ( !If_CutMergeOrdered( pCut1, pCut0, pCut, nLimit ) )
            return 0;
    }
    else
    {
        if ( !If_CutMergeOrdered( pCut0, pCut1, pCut, nLimit ) )
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

  Synopsis    [Computes delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutDelay( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    float Delay;
    int i;
    assert( pCut->nLeaves > 1 );
    Delay = -IF_FLOAT_LARGE;
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        Delay = IF_MAX( Delay, If_ObjCutBest(pLeaf)->Delay );
    return Delay + If_CutLutDelay(p, pCut);
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
    int i;
    printf( "{" );
    for ( i = 0; i < pCut->nLeaves; i++ )
        printf( " %d", pCut->pLeaves[i] );
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
    int * pArray;
    pArray = pCutDest->pLeaves;
    *pCutDest = *pCutSrc;
    pCutDest->pLeaves = pArray;
    memcpy( pCutDest->pLeaves, pCutSrc->pLeaves, sizeof(int) * pCutSrc->nLeaves );
}

/**Function*************************************************************

  Synopsis    [Finds the best cut.]

  Description [Mapping modes: delay (0), area flow (1), area (2).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMapping( If_Man_t * p, If_Obj_t * pObj, int Mode )
{
    If_Cut_t * pCut0, * pCut1, * pCut;
    int i, k, iCut;

    // prepare
    if ( Mode == 0 )
        pObj->EstRefs = (float)pObj->nRefs;
    else if ( Mode == 1 )
        pObj->EstRefs = (float)((2.0 * pObj->EstRefs + pObj->nRefs) / 3.0);
    else if ( Mode == 2 && pObj->nRefs > 0 )
        If_CutDeref( p, If_ObjCutBest(pObj), 100 );

    // recompute the parameters of the best cut
    p->nCuts = 0;
    p->nCutsMerged++;
    if ( Mode )
    {
        pCut = If_ObjCutBest(pObj);
        pCut->Delay = If_CutDelay( p, pCut );
        assert( pCut->Delay <= pObj->Required + p->fEpsilon );
        pCut->Area  = (Mode == 2)? If_CutAreaDerefed( p, pCut, 100 ) : If_CutFlow( p, pCut );
        // save the best cut from the previous iteration
        If_CutCopy( p->ppCuts[p->nCuts++], pCut );
        p->nCutsMerged++;
    }

    // prepare room for the next cut
    iCut = p->nCuts;
    pCut = p->ppCuts[iCut];
    // generate cuts
    If_ObjForEachCut( pObj->pFanin0, pCut0, i )
    If_ObjForEachCut( pObj->pFanin1, pCut1, k )
    {
        // make sure K-feasible cut exists
        if ( If_WordCountOnes(pCut0->uSign | pCut1->uSign) > p->pPars->nLutSize )
            continue;
        // prefilter using arrival times
        if ( Mode && (pCut0->Delay > pObj->Required + p->fEpsilon || pCut1->Delay > pObj->Required + p->fEpsilon) )
            continue;
        // merge the nodes
        if ( !If_CutMerge( pCut0, pCut1, pCut, p->pPars->nLutSize ) )
            continue;
        // check if this cut is contained in any of the available cuts
        pCut->uSign = pCut0->uSign | pCut1->uSign;
        if ( If_CutFilter( p, pCut, Mode ) )
            continue;
        // check if the cut satisfies the required times
        pCut->Delay = If_CutDelay( p, pCut );
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // the cuts have been successfully merged
        pCut->pOne = pCut0; pCut->fCompl0 = pObj->fCompl0;
        pCut->pTwo = pCut1; pCut->fCompl1 = pObj->fCompl1;
//        pCut->Phase = ...
//        pCut->Phase = (char)(int)If_CutAreaDerefed( p, pCut, 1 );
        pCut->Area  = (Mode == 2)? If_CutAreaDerefed( p, pCut, 100 ) : If_CutFlow( p, pCut );
        p->nCutsMerged++;
        // make sure the cut is the last one (after filtering it may not be so)
        assert( pCut == p->ppCuts[iCut] );
        p->ppCuts[iCut] = p->ppCuts[p->nCuts];
        p->ppCuts[p->nCuts] = pCut;
        // prepare room for the next cut
        iCut = ++p->nCuts;
        pCut = p->ppCuts[iCut];
    } 
//printf( "%d  ", p->nCuts );
    assert( p->nCuts > 0 );
    // sort if we have more cuts
    If_ManSortCuts( p, Mode );
    // decide how many cuts to use
    pObj->nCuts = IF_MIN( p->nCuts + 1, p->nCutsUsed );
    // take the first
    If_ObjForEachCutStart( pObj, pCut, i, 1 )
        If_CutCopy( pCut, p->ppCuts[i-1] );
    assert( If_ObjCutBest(pObj)->nLeaves > 1 );
    // assign delay of the trivial cut
    If_ObjCutTriv(pObj)->Delay = If_ObjCutBest(pObj)->Delay;
//printf( "%d %d   ", pObj->Id, (int)If_ObjCutBest(pObj)->Delay );
//printf( "%d %d   ", pObj->Id, pObj->nCuts );
    // ref the selected cut
    if ( Mode == 2 && pObj->nRefs > 0 )
        If_CutRef( p, If_ObjCutBest(pObj), 100 );
    // find the largest cut
    if ( p->nCutsMax < pObj->nCuts )
        p->nCutsMax = pObj->nCuts;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


