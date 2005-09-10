/**CFile****************************************************************

  FileName    [cutNode.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Procedures to compute cuts for a node.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutNode.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"
#include "cutList.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is contained in pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cut_CutCheckDominance( Cut_Cut_t * pDom, Cut_Cut_t * pCut )
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

  Synopsis    [Checks containment for one cut.]

  Description [Returns 1 if the cut is removed.]
               
  SideEffects [May remove other cuts in the set.]

  SeeAlso     []

***********************************************************************/
static inline int Cut_CutFilterOne( Cut_Man_t * p, Cut_List_t * pSuperList, Cut_Cut_t * pCut )
{
    Cut_Cut_t * pTemp, * pTemp2, ** ppTail;
    int a;

    // check if this cut is filtered out by smaller cuts
    for ( a = 2; a <= (int)pCut->nLeaves; a++ )
    {
        Cut_ListForEachCut( pSuperList->pHead[a], pTemp )
        {
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pTemp->uSign )
                continue;
            // check containment seriously
            if ( Cut_CutCheckDominance( pTemp, pCut ) )
            {
                p->nCutsFilter++;
                Cut_CutRecycle( p, pCut );
                return 1;
            }
        }
    }

    // filter out other cuts using this one
    for ( a = pCut->nLeaves + 1; a <= (int)pCut->nVarsMax; a++ )
    {
        ppTail = pSuperList->pHead + a;
        Cut_ListForEachCutSafe( pSuperList->pHead[a], pTemp, pTemp2 )
        {
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pCut->uSign )
            {
                ppTail = &pTemp->pNext;
                continue;
            }
            // check containment seriously
            if ( Cut_CutCheckDominance( pCut, pTemp ) )
            {
                p->nCutsFilter++;
                p->nNodeCuts--;
                // move the head
                if ( pSuperList->pHead[a] == pTemp )
                    pSuperList->pHead[a] = pTemp->pNext;
                // move the tail
                if ( pSuperList->ppTail[a] == &pTemp->pNext )
                    pSuperList->ppTail[a] = ppTail;
                // skip the given cut in the list
                *ppTail = pTemp->pNext;
                // recycle pTemp
                Cut_CutRecycle( p, pTemp );
            }
            else
                ppTail = &pTemp->pNext;
        }
        assert( ppTail == pSuperList->ppTail[a] );
        assert( *ppTail == NULL );
    }

    return 0;
}

/**Function*************************************************************

  Synopsis    [Filters cuts using dominance.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_CutFilter( Cut_Man_t * p, Cut_Cut_t * pList )
{ 
    Cut_Cut_t * pListR, ** ppListR = &pListR;
    Cut_Cut_t * pCut, * pCut2, * pDom, * pPrev;
    // save the first cut
    *ppListR = pList, ppListR = &pList->pNext;
    // try to filter out other cuts
    pPrev = pList;
    Cut_ListForEachCutSafe( pList->pNext, pCut, pCut2 )
    {
        assert( pCut->nLeaves > 1 );
        // go through all the previous cuts up to pCut
        Cut_ListForEachCutStop( pList->pNext, pDom, pCut )
        {
            if ( pDom->nLeaves > pCut->nLeaves )
                continue;
            if ( (pDom->uSign & pCut->uSign) != pDom->uSign )
                continue;
            if ( Cut_CutCheckDominance( pDom, pCut ) )
                break;
        }
        if ( pDom != pCut ) // pDom is contained in pCut - recycle pCut
        {
            // make sure cuts are connected after removing
            pPrev->pNext = pCut->pNext;
            // recycle the cut
            Cut_CutRecycle( p, pCut );
        }
        else // pDom is NOT contained in pCut - save pCut
        {
            *ppListR = pCut, ppListR = &pCut->pNext;
            pPrev = pCut;
        }
    }
    *ppListR = NULL;
}

/**Function*************************************************************

  Synopsis    [Processes two cuts.]

  Description [Returns 1 if the limit has been reached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cut_CutProcessTwo( Cut_Man_t * p, int Root, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1, Cut_List_t * pSuperList )
{
    Cut_Cut_t * pCut;
    int RetValue;
    // merge the cuts
    if ( pCut0->nLeaves >= pCut1->nLeaves )
        pCut = Cut_CutMergeTwo( p, pCut0, pCut1 );
    else
        pCut = Cut_CutMergeTwo( p, pCut1, pCut0 );
    if ( pCut == NULL )
        return 0;
    assert( pCut->nLeaves > 1 );
    // set the signature
    pCut->uSign = pCut0->uSign | pCut1->uSign;
    // check containment
    RetValue = p->pParams->fFilter && Cut_CutFilterOne( p, pSuperList, pCut );
    if ( RetValue )
        return 0;
    // compute the truth table
    if ( p->pParams->fTruth )
        Cut_TruthCompute( p, pCut, pCut0, pCut1 );
    // add to the list
    Cut_ListAdd( pSuperList, pCut );
    // return status (0 if okay; 1 if exceeded the limit)
    return ++p->nNodeCuts == p->pParams->nKeepMax;
}

/**Function*************************************************************

  Synopsis    [Computes the cuts by merging cuts at two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_NodeComputeCuts( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1 )
{
    Cut_List_t SuperList;
    Cut_Cut_t * pList0, * pList1, * pStop0, * pStop1, * pTemp0, * pTemp1;
    int i, Limit = p->pParams->nVarsMax;
    int clk = clock();
    assert( p->pParams->nVarsMax <= 6 );

    // start the new list
    Cut_ListStart( &SuperList );
    // get the cut lists of children
    pList0 = Cut_NodeReadCuts( p, Node0 );
    pList1 = Cut_NodeReadCuts( p, Node1 );
    assert( pList0 && pList1 );
    // get the simultation bit of the node
    p->fSimul = (fCompl0 ^ pList0->fSimul) & (fCompl1 ^ pList1->fSimul);
    // set temporary variables
    p->fCompl0 = fCompl0;
    p->fCompl1 = fCompl1;
    // find the point in the list where the max-var cuts begin
    Cut_ListForEachCut( pList0, pStop0 )
        if ( pStop0->nLeaves == (unsigned)Limit )
            break;
    Cut_ListForEachCut( pList1, pStop1 )
        if ( pStop1->nLeaves == (unsigned)Limit )
            break;
    // start with the elementary cut
    pTemp0 = Cut_CutCreateTriv( p, Node );
    Cut_ListAdd( &SuperList, pTemp0 );
    p->nNodeCuts = 1;
    // small by small
    Cut_ListForEachCutStop( pList0, pTemp0, pStop0 )
    Cut_ListForEachCutStop( pList1, pTemp1, pStop1 )
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    // small by large
    Cut_ListForEachCutStop( pList0, pTemp0, pStop0 )
    Cut_ListForEachCut( pStop1, pTemp1 )
    {
        if ( (pTemp0->uSign & pTemp1->uSign) != pTemp0->uSign )
            continue;
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    }
    // small by large
    Cut_ListForEachCutStop( pList1, pTemp1, pStop1 )
    Cut_ListForEachCut( pStop0, pTemp0 )
    {
        if ( (pTemp0->uSign & pTemp1->uSign) != pTemp1->uSign )
            continue;
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    }
    // large by large
    Cut_ListForEachCut( pStop0, pTemp0 )
    Cut_ListForEachCut( pStop1, pTemp1 )
    {
        assert( pTemp0->nLeaves == (unsigned)Limit && pTemp1->nLeaves == (unsigned)Limit );
        if ( pTemp0->uSign != pTemp1->uSign )
            continue;
        for ( i = 0; i < Limit; i++ )
            if ( pTemp0->pLeaves[i] != pTemp1->pLeaves[i] )
                break;
        if ( i < Limit )
            continue;
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    }
finish :
    if ( p->nNodeCuts == p->pParams->nKeepMax )
        p->nCutsLimit++;
    // set the list at the node
    Vec_PtrFillExtra( p->vCuts, Node + 1, NULL );
    assert( Cut_NodeReadCuts(p, Node) == NULL );
    pList0 = Cut_ListFinish( &SuperList );
    Cut_NodeWriteCuts( p, Node, pList0 );
    // consider dropping the fanins cuts
    if ( p->pParams->fDrop )
    {
        Cut_NodeTryDroppingCuts( p, Node0 );
        Cut_NodeTryDroppingCuts( p, Node1 );
    }
p->timeMerge += clock() - clk;
    // filter the cuts
clk = clock();
//    if ( p->pParams->fFilter )
//        Cut_CutFilter( p, pList0 );
p->timeFilter += clock() - clk;
    p->nNodes++;
    return pList0;
}

/**Function*************************************************************

  Synopsis    [Computes the cuts by unioning cuts at a choice node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_NodeUnionCuts( Cut_Man_t * p, Vec_Int_t * vNodes )
{
    Cut_List_t SuperList;
    Cut_Cut_t * pList, * pListStart, * pCut, * pCut2, * pTop;
    int i, k, Node, Root, Limit = p->pParams->nVarsMax;
    int clk = clock();

    assert( p->pParams->nVarsMax <= 6 );

    // start the new list
    Cut_ListStart( &SuperList );

    // remember the root node to save the resulting cuts
    Root = Vec_IntEntry( vNodes, 0 );
    p->nNodeCuts = 1;

    // collect small cuts first
    Vec_PtrClear( p->vTemp );
    Vec_IntForEachEntry( vNodes, Node, i )
    {
        // get the cuts of this node
        pList = Cut_NodeReadCuts( p, Node );
        Cut_NodeWriteCuts( p, Node, NULL );
        assert( pList );
        // remember the starting point
        pListStart = pList->pNext;
        pList->pNext = NULL;
        // save or recycle the elementary cut
        if ( i == 0 )
            Cut_ListAdd( &SuperList, pList ), pTop = pList;
        else
            Cut_CutRecycle( p, pList );
        // save all the cuts that are smaller than the limit
        Cut_ListForEachCutSafe( pListStart, pCut, pCut2 )
        {
            if ( pCut->nLeaves == (unsigned)Limit )
            {
                Vec_PtrPush( p->vTemp, pCut );
                break;
            }
            // check containment
            if ( p->pParams->fFilter && Cut_CutFilterOne( p, &SuperList, pCut ) )
                continue;
            // set the complemented bit by comparing the first cut with the current cut
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            pListStart = pCut->pNext;
            pCut->pNext = NULL;
            // add to the list
            Cut_ListAdd( &SuperList, pCut );
            if ( ++p->nNodeCuts == p->pParams->nKeepMax )
            {
                // recycle the rest of the cuts of this node
                Cut_ListForEachCutSafe( pListStart, pCut, pCut2 )
                    Cut_CutRecycle( p, pCut );
                // recycle all cuts of other nodes
                Vec_IntForEachEntryStart( vNodes, Node, k, i+1 )
                    Cut_NodeFreeCuts( p, Node );
                // recycle the saved cuts of other nodes
                Vec_PtrForEachEntry( p->vTemp, pList, k )
                    Cut_ListForEachCutSafe( pList, pCut, pCut2 )
                        Cut_CutRecycle( p, pCut );
                goto finish;
            }
        }
    } 
    // collect larger cuts next
    Vec_PtrForEachEntry( p->vTemp, pList, i )
    {
        Cut_ListForEachCutSafe( pList, pCut, pCut2 )
        {
            // check containment
            if ( p->pParams->fFilter && Cut_CutFilterOne( p, &SuperList, pCut ) )
                continue;
            // set the complemented bit
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            pListStart = pCut->pNext;
            pCut->pNext = NULL;
            // add to the list
            Cut_ListAdd( &SuperList, pCut );
            if ( ++p->nNodeCuts == p->pParams->nKeepMax )
            {
                // recycle the rest of the cuts
                Cut_ListForEachCutSafe( pListStart, pCut, pCut2 )
                    Cut_CutRecycle( p, pCut );
                // recycle the saved cuts of other nodes
                Vec_PtrForEachEntryStart( p->vTemp, pList, k, i+1 )
                    Cut_ListForEachCutSafe( pList, pCut, pCut2 )
                        Cut_CutRecycle( p, pCut );
                goto finish;
            }
        }
    }
finish :
    // set the cuts at the node
    assert( Cut_NodeReadCuts(p, Root) == NULL );
    pList = Cut_ListFinish( &SuperList );
    Cut_NodeWriteCuts( p, Root, pList );
p->timeUnion += clock() - clk;
    // filter the cuts
clk = clock();
//    if ( p->pParams->fFilter )
//        Cut_CutFilter( p, pList );
p->timeFilter += clock() - clk;
    p->nNodes -= vNodes->nSize - 1;
    return pList;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


