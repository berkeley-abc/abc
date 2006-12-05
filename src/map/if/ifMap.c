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

  Synopsis    [Finds the best cut.]

  Description [Mapping modes: delay (0), area flow (1), area (2).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMapping( If_Man_t * p, If_Obj_t * pObj, int Mode )
{
    If_Cut_t * pCut0, * pCut1, * pCut;
    int i, k, iCut, Temp;

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
        if ( !If_CutMerge( pCut0, pCut1, pCut ) )
            continue;
        // check if this cut is contained in any of the available cuts
        pCut->uSign = pCut0->uSign | pCut1->uSign;
        if ( If_CutFilter( p, pCut ) )
            continue;
        // check if the cut satisfies the required times
        pCut->Delay = If_CutDelay( p, pCut );
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // the cuts have been successfully merged
        // compute the truth table
        if ( p->pPars->fTruth )
            If_CutComputeTruth( p, pCut, pCut0, pCut1, pObj->fCompl0, pObj->fCompl1 );
        // compute the application-specific cost and depth
        Temp = p->pPars->pFuncCost? p->pPars->pFuncCost(If_CutTruth(pCut), pCut->nLimit) : 0;
        pCut->Cost = (Temp & 0xffff); pCut->Depth = (Temp >> 16);
        // compute area of the cut (this area may depend on the application specific cost)
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut, 100 ) : If_CutFlow( p, pCut );
        // make sure the cut is the last one (after filtering it may not be so)
        assert( pCut == p->ppCuts[iCut] );
        p->ppCuts[iCut] = p->ppCuts[p->nCuts];
        p->ppCuts[p->nCuts] = pCut;
        // count the cut
        p->nCuts++;
        p->nCutsMerged++;
        // prepare room for the next cut
        iCut = p->nCuts;
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


