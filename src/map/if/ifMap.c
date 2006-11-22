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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutMerge( If_Cut_t * pC0, If_Cut_t * pC1, If_Cut_t * pC, int nLimit )
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

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutCompareDelay( If_Cut_t ** ppC0, If_Cut_t ** ppC1 )
{
    If_Cut_t * pC0 = *ppC0;
    If_Cut_t * pC1 = *ppC1;
    if ( pC0->Delay < pC1->Delay )
        return -1;
    if ( pC0->Delay > pC1->Delay )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    if ( pC0->Flow < pC1->Flow )
        return -1;
    if ( pC0->Flow > pC1->Flow )
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
    if ( pC0->Flow < pC1->Flow )
        return -1;
    if ( pC0->Flow > pC1->Flow )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    if ( pC0->Delay < pC1->Delay )
        return -1;
    if ( pC0->Delay > pC1->Delay )
        return 1;
    return 0;
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
    Flow = If_CutLutArea(p, pCut);
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        Flow += If_ObjCutBest(pLeaf)->Flow / pLeaf->EstRefs;
    return Flow;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutArea1( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    float Area;
    int i;
    Area = If_CutLutArea(p, pCut);
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        if ( pLeaf->nRefs == 0 )
            Area += If_CutLutArea(p, If_ObjCutBest(pLeaf));
    return Area;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutRef1( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    int i;
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        pLeaf->nRefs++;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutDeref1( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    int i;
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        pLeaf->nRefs--;
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

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMapping( If_Man_t * p, If_Obj_t * pObj )
{
    If_Cut_t * pCut0, * pCut1, * pCut;
    int i, k;
    // create cross-product of the cuts
    p->nCuts = 0;
    pCut = p->ppCuts[0];
    If_ObjForEachCut( pObj->pFanin0, pCut0, i )
    If_ObjForEachCut( pObj->pFanin1, pCut1, k )
    {
        if ( pCut0->nLeaves < pCut1->nLeaves )
        {
            if ( !If_CutMerge( pCut1, pCut0, pCut, p->pPars->nLutSize ) )
                continue;
        }
        else
        {
            if ( !If_CutMerge( pCut0, pCut1, pCut, p->pPars->nLutSize ) )
                continue;
        }
        // the cuts have been successfully merged
        pCut->pOne = pCut0; pCut->fCompl0 = pObj->fCompl0;
        pCut->pTwo = pCut1; pCut->fCompl1 = pObj->fCompl1;
//        pCut->Phase = ...
        pCut->Delay = If_CutDelay( p, pCut );
        pCut->Flow  = If_CutFlow( p, pCut );
        // prepare room for the next cut
        pCut = p->ppCuts[++p->nCuts];
    } 
    // sort the cuts
    if ( p->pPars->Mode == 1 ) // delay
        qsort( p->ppCuts, p->nCuts, sizeof(If_Cut_t *), (int (*)(const void *, const void *))If_CutCompareDelay );
    else
        qsort( p->ppCuts, p->nCuts, sizeof(If_Cut_t *), (int (*)(const void *, const void *))If_CutCompareArea );
    // take the first
    pObj->nCuts = IF_MIN( p->nCuts + 1, p->pPars->nCutsMax );
    If_ObjForEachCutStart( pObj, pCut, i, 1 )
        If_CutCopy( pCut, p->ppCuts[i-1] );
    pObj->iCut = 1;
}

/**Function*************************************************************

  Synopsis    [Maps the nodes for delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMapping( If_Man_t * p )
{
    If_Obj_t * pObj;
    float DelayBest;
    int i, clk = clock();
    // set arrival times and trivial cuts at const 1 and PIs
    If_ManConst1(p)->Cuts[0].Delay = 0.0;
    If_ManForEachPi( p, pObj, i )
        pObj->Cuts[0].Delay = p->pPars->pTimesArr[i];
    // set the initial fanout estimates
    If_ManForEachObj( p, pObj, i )
        pObj->EstRefs = (float)pObj->nRefs;
    // map the internal nodes
    If_ManForEachNode( p, pObj, i )
        If_ObjPerformMapping( p, pObj );
    // get the best arrival time of the POs
    DelayBest = If_ManDelayMax(p);
    printf( "Best delay = %d. ", (int)DelayBest );
    PRT( "Time", clock() - clk );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


