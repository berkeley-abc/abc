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


ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

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

  Synopsis    [Counts the number of 1s in the signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutDelaySpecial( If_Man_t * p, If_Cut_t * pCut, int fCarry )
{
    static float Pin2Pin[2][3] = { {1.0, 1.0, 1.0}, {1.0, 1.0, 0.0} };
    If_Obj_t * pLeaf;
    float DelayCur, Delay = -IF_FLOAT_LARGE;
    int i;
    assert( pCut->nLeaves <= 3 );
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        DelayCur = If_ObjCutBest(pLeaf)->Delay;
        Delay = IF_MAX( Delay, Pin2Pin[fCarry][i] + DelayCur );
    }
    return Delay;
 }

/**Function*************************************************************

  Synopsis    [Finds the best cut for the given node.]

  Description [Mapping modes: delay (0), area flow (1), area (2).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingAnd( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess )
{
    If_Set_t * pCutSet;
    If_Cut_t * pCut0, * pCut1, * pCut;
    int i, k;

//    assert( p->pPars->fSeqMap || !If_ObjIsAnd(pObj->pFanin0) || pObj->pFanin0->pCutSet->nCuts > 1 );
//    assert( p->pPars->fSeqMap || !If_ObjIsAnd(pObj->pFanin1) || pObj->pFanin1->pCutSet->nCuts > 1 );

    assert( p->pPars->fSeqMap || !If_ObjIsAnd(pObj->pFanin0) || pObj->pFanin0->pCutSet->nCuts > 0 );
    assert( p->pPars->fSeqMap || !If_ObjIsAnd(pObj->pFanin1) || pObj->pFanin1->pCutSet->nCuts > 0 );

    // prepare
    if ( !p->pPars->fSeqMap )
    {
        if ( Mode == 0 )
            pObj->EstRefs = (float)pObj->nRefs;
        else if ( Mode == 1 )
            pObj->EstRefs = (float)((2.0 * pObj->EstRefs + pObj->nRefs) / 3.0);
    }
/*
    // process special cut
    if ( p->pDriverCuts && p->pDriverCuts[pObj->Id] )
    {
        pCut = If_ObjCutBest(pObj);
        if ( pCut->nLeaves == 0 )
        {
            pCut->nLeaves = Vec_IntSize( p->pDriverCuts[pObj->Id] );
            Vec_IntForEachEntry( p->pDriverCuts[pObj->Id], k, i )
                pCut->pLeaves[i] = k;
            assert( pCut->pLeaves[0] <= pCut->pLeaves[1] );
//            if ( pObj->nRefs > 0 )
//                If_CutAreaRef( p, pCut );
        }
        pCut->Delay = If_CutDelaySpecial( p, pCut, pObj->fDriver );
        pCut->Area  = (Mode == 2)? 1 : If_CutAreaFlow( p, pCut );
        if ( p->pPars->fEdge )
            pCut->Edge = (Mode == 2)? 3 : If_CutEdgeFlow( p, pCut );
        if ( p->pPars->fPower )
            pCut->Power  = (Mode == 2)? 0 : If_CutPowerFlow( p, pCut, pObj );

        // prepare the cutset
        pCutSet = If_ManSetupNodeCutSet( p, pObj );
        // copy best cut
        If_CutCopy( p, pCutSet->ppCuts[pCutSet->nCuts++], If_ObjCutBest(pObj) );
        // add the trivial cut to the set
        If_ManSetupCutTriv( p, pCutSet->ppCuts[pCutSet->nCuts++], pObj->Id );
        // free the cuts
        If_ManDerefNodeCutSet( p, pObj );
        assert( pCutSet->nCuts == 2 );
        return;
    }
*/
    // deref the selected cut
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaDeref( p, If_ObjCutBest(pObj) );

    // prepare the cutset
    pCutSet = If_ManSetupNodeCutSet( p, pObj );

    // get the current assigned best cut
    pCut = If_ObjCutBest(pObj);
    if ( pCut->nLeaves > 0 )
    {
        // recompute the parameters of the best cut
///        if ( p->pPars->pLutStruct )
///            pCut->Delay = If_CutDelayLutStruct( p, pCut, p->pPars->pLutStruct, p->pPars->WireDelay );
//        else if ( p->pPars->fDelayOpt )
        if ( p->pPars->fUserRecLib )
            pCut->Delay = If_CutDelayRecCost(p, pCut, pObj);
        else if(p->pPars->fDelayOpt)
            pCut->Delay = If_CutDelaySopCost(p,pCut);
        else
            pCut->Delay = If_CutDelay( p, pObj, pCut );
//        assert( pCut->Delay <= pObj->Required + p->fEpsilon );
        if ( pCut->Delay > pObj->Required + 2*p->fEpsilon )
            Abc_Print( 1, "If_ObjPerformMappingAnd(): Warning! Delay of node %d (%f) exceeds the required times (%f).\n", 
                pObj->Id, pCut->Delay, pObj->Required + p->fEpsilon );
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut ) : If_CutAreaFlow( p, pCut );
        if ( p->pPars->fEdge )
            pCut->Edge = (Mode == 2)? If_CutEdgeDerefed( p, pCut ) : If_CutEdgeFlow( p, pCut );
        if ( p->pPars->fPower )
            pCut->Power = (Mode == 2)? If_CutPowerDerefed( p, pCut, pObj ) : If_CutPowerFlow( p, pCut, pObj );
        // save the best cut from the previous iteration
        if ( !fPreprocess )
            If_CutCopy( p, pCutSet->ppCuts[pCutSet->nCuts++], pCut );
    }

    // generate cuts
    If_ObjForEachCut( pObj->pFanin0, pCut0, i )
    If_ObjForEachCut( pObj->pFanin1, pCut1, k )
    {
        // get the next free cut
        assert( pCutSet->nCuts <= pCutSet->nCutsMax );
        pCut = pCutSet->ppCuts[pCutSet->nCuts];
        // make sure K-feasible cut exists
        if ( If_WordCountOnes(pCut0->uSign | pCut1->uSign) > p->pPars->nLutSize )
            continue;
        // merge the cuts
        if ( !If_CutMerge( pCut0, pCut1, pCut ) )
            continue;
        if ( pObj->fSpec && pCut->nLeaves == (unsigned)p->pPars->nLutSize )
            continue;
        assert( p->pPars->fSeqMap || pCut->nLeaves > 1 );
        p->nCutsMerged++;
        p->nCutsTotal++;
        // check if this cut is contained in any of the available cuts
//        if ( p->pPars->pFuncCost == NULL && If_CutFilter( p, pCut ) ) // do not filter functionality cuts
        if ( !p->pPars->fSkipCutFilter && If_CutFilter( pCutSet, pCut ) )
            continue;
        // compute the truth table
        pCut->fCompl = 0;
        if ( p->pPars->fTruth )
        {
//            int clk = clock();
            int RetValue = If_CutComputeTruth( p, pCut, pCut0, pCut1, pObj->fCompl0, pObj->fCompl1 );
//            p->timeTruth += clock() - clk;
            pCut->fUseless = 0;
            if ( p->pPars->pFuncCell && RetValue < 2 )
            {
                assert( pCut->nLimit >= 4 && pCut->nLimit <= 16 );
                pCut->fUseless = !p->pPars->pFuncCell( p, If_CutTruth(pCut), pCut->nLimit, pCut->nLeaves, p->pPars->pLutStruct );
                p->nCutsUselessAll += pCut->fUseless;
                p->nCutsUseless[pCut->nLeaves] += pCut->fUseless;
                p->nCutsCountAll++;
                p->nCutsCount[pCut->nLeaves]++;
            }

        }
        
        // compute the application-specific cost and depth
        pCut->fUser = (p->pPars->pFuncCost != NULL);
        pCut->Cost = p->pPars->pFuncCost? p->pPars->pFuncCost(pCut) : 0;
        if ( pCut->Cost == IF_COST_MAX )
            continue;
        // check if the cut satisfies the required times
///        if ( p->pPars->pLutStruct )
///            pCut->Delay = If_CutDelayLutStruct( p, pCut, p->pPars->pLutStruct, p->pPars->WireDelay );
//        else if ( p->pPars->fDelayOpt )
        if ( p->pPars->fUserRecLib )
            pCut->Delay = If_CutDelayRecCost(p, pCut, pObj);
        else if (p->pPars->fDelayOpt)
            pCut->Delay = If_CutDelaySopCost(p, pCut);  
        else
            pCut->Delay = If_CutDelay( p, pObj, pCut );
        //if ( pCut->Cost == IF_COST_MAX )
       //     continue;
//        Abc_Print( 1, "%.2f ", pCut->Delay );
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // compute area of the cut (this area may depend on the application specific cost)
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut ) : If_CutAreaFlow( p, pCut );
        if ( p->pPars->fEdge )
            pCut->Edge = (Mode == 2)? If_CutEdgeDerefed( p, pCut ) : If_CutEdgeFlow( p, pCut );
        if ( p->pPars->fPower )
            pCut->Power = (Mode == 2)? If_CutPowerDerefed( p, pCut, pObj ) : If_CutPowerFlow( p, pCut, pObj );
        pCut->AveRefs = (Mode == 0)? (float)0.0 : If_CutAverageRefs( p, pCut );
        // insert the cut into storage
        If_CutSort( p, pCutSet, pCut );
    } 
    assert( pCutSet->nCuts > 0 );

    // add the trivial cut to the set
    if ( !pObj->fSkipCut )
    {
        If_ManSetupCutTriv( p, pCutSet->ppCuts[pCutSet->nCuts++], pObj->Id );
        assert( pCutSet->nCuts <= pCutSet->nCutsMax+1 );
    }

    // update the best cut
    if ( !fPreprocess || pCutSet->ppCuts[0]->Delay <= pObj->Required + p->fEpsilon )
    {
        If_CutCopy( p, If_ObjCutBest(pObj), pCutSet->ppCuts[0] );
        if(p->pPars->fUserRecLib)
            assert(If_ObjCutBest(pObj)->Cost < IF_COST_MAX && If_ObjCutBest(pObj)->Delay < ABC_INFINITY);
    }
    assert( p->pPars->fSeqMap || If_ObjCutBest(pObj)->nLeaves > 1 );
    // ref the selected cut
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaRef( p, If_ObjCutBest(pObj) );
    if ( If_ObjCutBest(pObj)->fUseless )
        Abc_Print( 1, "The best cut is useless.\n" );

    // call the user specified function for each cut
    if ( p->pPars->pFuncUser )
        If_ObjForEachCut( pObj, pCut, i )
            p->pPars->pFuncUser( p, pObj, pCut );


    // free the cuts
    If_ManDerefNodeCutSet( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Finds the best cut for the choice node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingChoice( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess )
{
    If_Set_t * pCutSet;
    If_Obj_t * pTemp;
    If_Cut_t * pCutTemp, * pCut;
    int i;
    assert( pObj->pEquiv != NULL );

    // prepare
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaDeref( p, If_ObjCutBest(pObj) );

    // remove elementary cuts
    for ( pTemp = pObj; pTemp; pTemp = pTemp->pEquiv )
        pTemp->pCutSet->nCuts--;

    // update the cutset of the node
    pCutSet = pObj->pCutSet;

    // generate cuts
    for ( pTemp = pObj->pEquiv; pTemp; pTemp = pTemp->pEquiv )
    {
        assert( pTemp->nRefs == 0 );
//        assert( p->pPars->fSeqMap || pTemp->pCutSet->nCuts > 0 ); // June 9, 2009
        if ( pTemp->pCutSet->nCuts == 0 )
            continue;
        // go through the cuts of this node
        If_ObjForEachCut( pTemp, pCutTemp, i )
        {
            assert( p->pPars->fSeqMap || pCutTemp->nLeaves > 1 );
            // get the next free cut
            assert( pCutSet->nCuts <= pCutSet->nCutsMax );
            pCut = pCutSet->ppCuts[pCutSet->nCuts];
            // copy the cut into storage
            If_CutCopy( p, pCut, pCutTemp );
            // check if this cut is contained in any of the available cuts
            if ( If_CutFilter( pCutSet, pCut ) )
                continue;
            // check if the cut satisfies the required times
            assert( pCut->Delay == If_CutDelay( p, pTemp, pCut ) );
            if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
                continue;
            // set the phase attribute
            assert( pCut->fCompl == 0 );
            pCut->fCompl ^= (pObj->fPhase ^ pTemp->fPhase); // why ^= ?
            // compute area of the cut (this area may depend on the application specific cost)
            pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut ) : If_CutAreaFlow( p, pCut );
            if ( p->pPars->fEdge )
                pCut->Edge = (Mode == 2)? If_CutEdgeDerefed( p, pCut ) : If_CutEdgeFlow( p, pCut );
            if ( p->pPars->fPower )
                pCut->Power = (Mode == 2)? If_CutPowerDerefed( p, pCut, pObj ) : If_CutPowerFlow( p, pCut, pObj );
            pCut->AveRefs = (Mode == 0)? (float)0.0 : If_CutAverageRefs( p, pCut );
            // insert the cut into storage
            If_CutSort( p, pCutSet, pCut );
        }
    } 
    assert( pCutSet->nCuts > 0 );

    // add the trivial cut to the set
    if ( !pObj->fSkipCut )
    {
        If_ManSetupCutTriv( p, pCutSet->ppCuts[pCutSet->nCuts++], pObj->Id );
        assert( pCutSet->nCuts <= pCutSet->nCutsMax+1 );
    }

    // update the best cut
    if ( !fPreprocess || pCutSet->ppCuts[0]->Delay <= pObj->Required + p->fEpsilon )
        If_CutCopy( p, If_ObjCutBest(pObj), pCutSet->ppCuts[0] );
    assert( p->pPars->fSeqMap || If_ObjCutBest(pObj)->nLeaves > 1 );

    // ref the selected cut
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaRef( p, If_ObjCutBest(pObj) );

    // free the cuts
    If_ManDerefChoiceCutSet( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Performs one mapping pass over all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode, int fPreprocess, char * pLabel )
{
//    ProgressBar * pProgress;
    If_Obj_t * pObj;
    int i, clk = clock();
    float arrTime;
    assert( Mode >= 0 && Mode <= 2 );
    // set the sorting function
    if ( Mode || p->pPars->fArea ) // area
        p->SortMode = 1;
    else if ( p->pPars->fFancy )
        p->SortMode = 2;
    else
        p->SortMode = 0;
    // set the cut number
    p->nCutsUsed   = nCutsUsed;
    p->nCutsMerged = 0;
    // make sure the visit counters are all zero
    If_ManForEachNode( p, pObj, i )
        assert( pObj->nVisits == pObj->nVisitsCopy );
    // map the internal nodes
    if ( p->pManTim != NULL )
    {
        Tim_ManIncrementTravId( p->pManTim );
        If_ManForEachObj( p, pObj, i )
        {
            if ( If_ObjIsAnd(pObj) )
            {
                If_ObjPerformMappingAnd( p, pObj, Mode, fPreprocess );
                if ( pObj->fRepr )
                    If_ObjPerformMappingChoice( p, pObj, Mode, fPreprocess );
            }
            else if ( If_ObjIsCi(pObj) )
            {
//Abc_Print( 1, "processing CI %d\n", pObj->Id );
                arrTime = Tim_ManGetCiArrival( p->pManTim, pObj->IdPio );
                If_ObjSetArrTime( pObj, arrTime );
            }
            else if ( If_ObjIsCo(pObj) )
            {
                arrTime = If_ObjArrTime( If_ObjFanin0(pObj) );
                Tim_ManSetCoArrival( p->pManTim, pObj->IdPio, arrTime );
            }
            else if ( If_ObjIsConst1(pObj) )
            {
            }
            else
                assert( 0 );
        }
//        Tim_ManPrint( p->pManTim );
    }
    else
    {
    //    pProgress = Extra_ProgressBarStart( stdout, If_ManObjNum(p) );
        If_ManForEachNode( p, pObj, i )
        {
    //        Extra_ProgressBarUpdate( pProgress, i, pLabel );
            If_ObjPerformMappingAnd( p, pObj, Mode, fPreprocess );
            if ( pObj->fRepr )
                If_ObjPerformMappingChoice( p, pObj, Mode, fPreprocess );
        }
    }
//    Extra_ProgressBarStop( pProgress );
    // make sure the visit counters are all zero
    If_ManForEachNode( p, pObj, i )
        assert( pObj->nVisits == 0 );
    // compute required times and stats
    If_ManComputeRequired( p );
//    Tim_ManPrint( p->pManTim );
    if ( p->pPars->fVerbose )
    {
        char Symb = fPreprocess? 'P' : ((Mode == 0)? 'D' : ((Mode == 1)? 'F' : 'A'));
        Abc_Print( 1, "%c: Del = %7.2f. Ar = %9.1f. Edge = %8d. Switch = %7.2f. Cut = %8d. ", 
            Symb, p->RequiredGlo, p->AreaGlo, p->nNets, p->dPower, p->nCutsMerged );
        Abc_PrintTime( 1, "T", clock() - clk );
//    Abc_Print( 1, "Max number of cuts = %d. Average number of cuts = %5.2f.\n", 
//        p->nCutsMax, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

