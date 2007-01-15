/**CFile****************************************************************

  FileName    [ifPrepro.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Selects the starting mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifPrepro.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void If_ManPerformMappingMoveBestCut( If_Man_t * p, int iPosNew, int iPosOld );
static void If_ManPerformMappingAdjust( If_Man_t * p, int nCuts );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Merges the results of delay, relaxed delay and area-based mapping.]

  Description [Delay target may be different from minimum delay!!!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManPerformMappingPreprocess( If_Man_t * p )
{
    float delayArea, delayDelay, delayPure;
    int clk = clock();
    assert( p->pPars->nCutsMax >= 4 );

    // perform min-area mapping and move the cut to the end
    p->pPars->fArea = 1;
    If_ManPerformMappingRound( p, p->pPars->nCutsMax, 0, 0, "Start delay" );
    p->pPars->fArea = 0;
    delayArea = If_ManDelayMax( p, 0 );
    if ( p->pPars->DelayTarget != -1 && delayArea < p->pPars->DelayTarget - p->fEpsilon )
        delayArea = p->pPars->DelayTarget;
    If_ManPerformMappingMoveBestCut( p, p->pPars->nCutsMax - 1, 1 );

    // perfrom min-delay mapping and move the cut to the end
    p->pPars->fFancy = 1;
    If_ManPerformMappingRound( p, p->pPars->nCutsMax - 1, 0, 0, "Start delay-2" );
    p->pPars->fFancy = 0;
    delayDelay = If_ManDelayMax( p, 0 );
    if ( p->pPars->DelayTarget != -1 && delayDelay < p->pPars->DelayTarget - p->fEpsilon )
        delayDelay = p->pPars->DelayTarget;
    If_ManPerformMappingMoveBestCut( p, p->pPars->nCutsMax - 2, 1 );

    // perform min-delay mapping
    If_ManPerformMappingRound( p, p->pPars->nCutsMax - 2, 0, 0, "Start flow" );
    delayPure = If_ManDelayMax( p, 0 );
    if ( p->pPars->DelayTarget != -1 && delayPure < p->pPars->DelayTarget - p->fEpsilon )
        delayPure = p->pPars->DelayTarget;

    // decide what to do
    if ( delayPure < delayDelay - p->fEpsilon && delayPure < delayArea - p->fEpsilon )
    {
        // copy the remaining two cuts
        if ( p->pPars->nCutsMax > 4 )
        {
            If_ManPerformMappingMoveBestCut( p, 2, p->pPars->nCutsMax - 2 );
            If_ManPerformMappingMoveBestCut( p, 3, p->pPars->nCutsMax - 1 );
        }
        If_ManComputeRequired( p, 1 );
        If_ManPerformMappingAdjust( p, 4 );
    }
    else if ( delayDelay < delayArea - p->fEpsilon )
    {
        If_ManPerformMappingMoveBestCut( p, 1, p->pPars->nCutsMax - 2 );
        If_ManPerformMappingMoveBestCut( p, 2, p->pPars->nCutsMax - 1 );
        If_ManComputeRequired( p, 1 );
        If_ManPerformMappingAdjust( p, 3 );
    }
    else
    {
        If_ManPerformMappingMoveBestCut( p, 1, p->pPars->nCutsMax - 1 );
        If_ManComputeRequired( p, 1 );
        If_ManPerformMappingAdjust( p, 2 );
    }
    If_ManComputeRequired( p, 1 );
    if ( p->pPars->fVerbose )
    {
        printf( "S:  Del = %6.2f. Area = %8.2f. Nets = %6d. Cuts = %8d. Lim = %2d. Ave = %5.2f. ", 
            p->RequiredGlo, p->AreaGlo, p->nNets, p->nCutsMerged, p->nCutsUsed, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
        PRT( "T", clock() - clk );
    }
}

/**Function*************************************************************

  Synopsis    [Moves the best cut to the given position.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManPerformMappingMoveBestCut( If_Man_t * p, int iPosNew, int iPosOld )
{
    If_Obj_t * pObj;
    int i;
    assert( iPosOld != iPosNew );
    assert( iPosOld > 0 && iPosOld < p->pPars->nCutsMax );
    assert( iPosNew > 0 && iPosNew < p->pPars->nCutsMax );
    If_ManForEachNode( p, pObj, i )
        If_CutCopy( pObj->Cuts + iPosNew, pObj->Cuts + iPosOld );
}

/**Function*************************************************************

  Synopsis    [Adjusts mapping for the given cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManPerformMappingAdjust( If_Man_t * p, int nCuts )
{
    If_Cut_t * pCut, * pCutBest;
    If_Obj_t * pObj;
    int i, c;
    assert( nCuts >= 2 && nCuts <= 4 );
    If_ManForEachNode( p, pObj, i )
    {
        pCutBest = NULL;
        for ( c = 1; c < nCuts; c++ )
        {
            pCut = pObj->Cuts + c;
            pCut->Delay = If_CutDelay( p, pCut );
            pCut->Area  = If_CutFlow( p, pCut );
            assert( pCutBest || pCut->Delay < pObj->Required + p->fEpsilon );
            if ( pCutBest == NULL || 
                (pCut->Delay < pObj->Required + p->fEpsilon && 
                 pCut->Area < pCutBest->Area - p->fEpsilon) )
                pCutBest = pCut;
        }
        assert( pCutBest != NULL );
        // check if we need to move
        if ( pCutBest != pObj->Cuts + 1 )
            If_CutCopy( pObj->Cuts + 1, pCutBest );
        // set the number of cuts
        pObj->nCuts = 2;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


