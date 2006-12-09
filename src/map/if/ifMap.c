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
  - use average nrefs for tie-breaking

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

  Synopsis    [Finds the best cut for the given node.]

  Description [Mapping modes: delay (0), area flow (1), area (2).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMapping( If_Man_t * p, If_Obj_t * pObj, int Mode )
{
    If_Cut_t * pCut0, * pCut1, * pCut;
    int i, k, iCut;

    assert( !If_ObjIsAnd(pObj->pFanin0) || pObj->pFanin0->nCuts > 1 );
    assert( !If_ObjIsAnd(pObj->pFanin1) || pObj->pFanin1->nCuts > 1 );

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
        // merge the nodes
        if ( !If_CutMerge( pCut0, pCut1, pCut ) )
            continue;
        // check if this cut is contained in any of the available cuts
        pCut->uSign = pCut0->uSign | pCut1->uSign;
        pCut->fCompl = 0;
//        if ( p->pPars->pFuncCost == NULL && If_CutFilter( p, pCut ) ) // do not filter functionality cuts
        if ( If_CutFilter( p, pCut ) )
            continue;
        // the cuts have been successfully merged
        // compute the truth table
        if ( p->pPars->fTruth )
            If_CutComputeTruth( p, pCut, pCut0, pCut1, pObj->fCompl0, pObj->fCompl1 );
        // compute the application-specific cost and depth
        pCut->fUser = (p->pPars->pFuncCost != NULL);
        pCut->Cost = p->pPars->pFuncCost? p->pPars->pFuncCost(pCut) : 0;
        // check if the cut satisfies the required times
        pCut->Delay = If_CutDelay( p, pCut );
//        printf( "%.2f ", pCut->Delay );
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // compute area of the cut (this area may depend on the application specific cost)
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut, 100 ) : If_CutFlow( p, pCut );
        pCut->AveRefs = (Mode == 0)? (float)0.0 : If_CutAverageRefs( p, pCut );
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
    assert( p->nCuts > 0 );
    // sort if we have more cuts
    If_ManSortCuts( p, Mode );
    // decide how many cuts to use
    pObj->nCuts = IF_MIN( p->nCuts + 1, p->nCutsUsed );
    // take the first
    If_ObjForEachCutStart( pObj, pCut, i, 1 )
        If_CutCopy( pCut, p->ppCuts[i-1] );
    assert( If_ObjCutBest(pObj)->nLeaves > 1 );
    // ref the selected cut
    if ( Mode == 2 && pObj->nRefs > 0 )
        If_CutRef( p, If_ObjCutBest(pObj), 100 );
    // find the largest cut
    if ( p->nCutsMax < pObj->nCuts )
        p->nCutsMax = pObj->nCuts;
}

/**Function*************************************************************

  Synopsis    [Finds the best cut for the choice node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjMergeChoice( If_Man_t * p, If_Obj_t * pObj, int Mode )
{
    If_Obj_t * pTemp;
    If_Cut_t * pCutTemp, * pCut;
    int i, iCut;
    assert( pObj->pEquiv != NULL );
    // prepare
    if ( Mode == 2 && pObj->nRefs > 0 )
        If_CutDeref( p, If_ObjCutBest(pObj), 100 );
    // prepare room for the next cut
    p->nCuts = 0;
    iCut = p->nCuts;
    pCut = p->ppCuts[iCut];
    // generate cuts
    for ( pTemp = pObj; pTemp; pTemp = pTemp->pEquiv )
    If_ObjForEachCutStart( pTemp, pCutTemp, i, 1 )
    {
        assert( pTemp->nCuts > 1 );
        assert( pTemp == pObj || pTemp->nRefs == 0 );
        // copy the cut into storage
        If_CutCopy( pCut, pCutTemp );
        // check if this cut is contained in any of the available cuts
        if ( If_CutFilter( p, pCut ) )
            continue;
        // the cuts have been successfully merged
        // check if the cut satisfies the required times
        assert( pCut->Delay == If_CutDelay( p, pCut ) );
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // set the phase attribute
        pCut->fCompl ^= (pObj->fPhase ^ pTemp->fPhase);
        // compute area of the cut (this area may depend on the application specific cost)
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut, 100 ) : If_CutFlow( p, pCut );
        pCut->AveRefs = (Mode == 0)? (float)0.0 : If_CutAverageRefs( p, pCut );
        // make sure the cut is the last one (after filtering it may not be so)
        assert( pCut == p->ppCuts[iCut] );
        p->ppCuts[iCut] = p->ppCuts[p->nCuts];
        p->ppCuts[p->nCuts] = pCut;
        // count the cut
        p->nCuts++;
        // prepare room for the next cut
        iCut = p->nCuts;
        pCut = p->ppCuts[iCut];
        // quit if we exceeded the number of cuts
        if ( p->nCuts >= p->pPars->nCutsMax * p->pPars->nCutsMax )
            break;
    } 
    assert( p->nCuts > 0 );
    // sort if we have more cuts
    If_ManSortCuts( p, Mode );
    // decide how many cuts to use
    pObj->nCuts = IF_MIN( p->nCuts + 1, p->nCutsUsed );
    // take the first
    If_ObjForEachCutStart( pObj, pCut, i, 1 )
        If_CutCopy( pCut, p->ppCuts[i-1] );
    assert( If_ObjCutBest(pObj)->nLeaves > 1 );
    // ref the selected cut
    if ( Mode == 2 && pObj->nRefs > 0 )
        If_CutRef( p, If_ObjCutBest(pObj), 100 );
    // find the largest cut
    if ( p->nCutsMax < pObj->nCuts )
        p->nCutsMax = pObj->nCuts;
}

/**Function*************************************************************

  Synopsis    [Performs one mapping pass over all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode, int fRequired, char * pLabel )
{
    ProgressBar * pProgress;
    If_Obj_t * pObj;
    int i, clk = clock();
    assert( Mode >= 0 && Mode <= 2 );
    // set the cut number
    p->nCutsUsed   = nCutsUsed;
    p->nCutsMerged = 0;
    p->nCutsSaved  = 0;
    p->nCutsMax    = 0;
    // map the internal nodes
    pProgress = Extra_ProgressBarStart( stdout, If_ManObjNum(p) );
    If_ManForEachNode( p, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, pLabel );
        If_ObjPerformMapping( p, pObj, Mode );
        if ( pObj->fRepr )
            If_ObjMergeChoice( p, pObj, Mode );
    }
    Extra_ProgressBarStop( pProgress );
    // compute required times and stats
    if ( fRequired )
    {
        If_ManComputeRequired( p, Mode==0 );
        if ( p->pPars->fVerbose )
        {
            char Symb = (Mode == 0)? 'D' : ((Mode == 1)? 'F' : 'A');
            printf( "%c:  Del = %6.2f. Area = %8.2f. Cuts = %8d. Lim = %2d. Ave = %5.2f. ", 
                Symb, p->RequiredGlo, p->AreaGlo, p->nCutsMerged, p->nCutsUsed, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
            PRT( "T", clock() - clk );
//            printf( "Saved cuts = %d.\n", p->nCutsSaved );
//    printf( "Max number of cuts = %d. Average number of cuts = %5.2f.\n", 
//        p->nCutsMax, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
        }
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


