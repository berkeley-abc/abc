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

  Synopsis    [Checks containment for one cut.]

  Description [Returns 1 if the cut is removed.]
               
  SideEffects [May remove other cuts in the set.]

  SeeAlso     []

***********************************************************************/
static inline int Cut_CutFilterOld( Cut_Man_t * p, Cut_Cut_t * pList, Cut_Cut_t * pCut )
{
    Cut_Cut_t * pPrev, * pTemp, * pTemp2, ** ppTail;

    // check if this cut is filtered out by smaller cuts
    pPrev = NULL;
    Cut_ListForEachCut( pList, pTemp )
    {
        if ( pTemp->nLeaves > pCut->nLeaves )
            break;
        pPrev = pTemp;
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
    assert( pPrev->pNext == pTemp );

    // filter out other cuts using this one
    ppTail = &pPrev->pNext;
    Cut_ListForEachCutSafe( pTemp, pTemp, pTemp2 )
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
            // skip the given cut in the list
            *ppTail = pTemp->pNext;
            // recycle pTemp
            Cut_CutRecycle( p, pTemp );
        }
        else
            ppTail = &pTemp->pNext;
    }
    assert( *ppTail == NULL );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Processes two cuts.]

  Description [Returns 1 if the limit has been reached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cut_CutProcessTwo( Cut_Man_t * p, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1, Cut_List_t * pSuperList )
{
    Cut_Cut_t * pCut;
    // merge the cuts
    if ( pCut0->nLeaves >= pCut1->nLeaves )
        pCut = Cut_CutMergeTwo( p, pCut0, pCut1 );
    else
        pCut = Cut_CutMergeTwo( p, pCut1, pCut0 );
    if ( pCut == NULL )
        return 0;
    assert( p->pParams->fSeq || pCut->nLeaves > 1 );
    // set the signature
    pCut->uSign = pCut0->uSign | pCut1->uSign;
    if ( p->pParams->fRecord )
        pCut->Num0 = pCut0->Num0, pCut->Num1 = pCut1->Num0;
    // check containment
    if ( p->pParams->fFilter )
    {
        if ( Cut_CutFilterOne(p, pSuperList, pCut) )
            return 0;
        if ( p->pParams->fSeq )
        {
            if ( p->pCompareOld && Cut_CutFilterOld(p, p->pCompareOld, pCut) )
                return 0;
            if ( p->pCompareNew && Cut_CutFilterOld(p, p->pCompareNew, pCut) )
                return 0;
        }
    }
    // compute the truth table
    if ( p->pParams->fTruth )
        Cut_TruthCompute( pCut, pCut0, pCut1, p->fCompl0, p->fCompl1 );
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
Cut_Cut_t * Cut_NodeComputeCuts( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1, int fTriv )
{
    Cut_List_t Super, * pSuper = &Super;
    Cut_Cut_t * pList, * pCut;
    int clk;
    // start the number of cuts at the node
    p->nNodes++;
    p->nNodeCuts = 0;
    // prepare information for recording
    if ( p->pParams->fRecord )
    {
        Cut_CutNumberList( Cut_NodeReadCutsNew(p, Node0) );
        Cut_CutNumberList( Cut_NodeReadCutsNew(p, Node1) );
    }
    // compute the cuts
clk = clock();
    Cut_ListStart( pSuper );
    Cut_NodeDoComputeCuts( p, pSuper, Node, fCompl0, fCompl1, Cut_NodeReadCutsNew(p, Node0), Cut_NodeReadCutsNew(p, Node1), fTriv );
    pList = Cut_ListFinish( pSuper );
p->timeMerge += clock() - clk;
    // verify the result of cut computation
//    Cut_CutListVerify( pList );
    // performing the recording
    if ( p->pParams->fRecord )
    {
        Vec_IntWriteEntry( p->vNodeStarts, Node, Vec_IntSize(p->vCutPairs) );
        Cut_ListForEachCut( pList, pCut )
            Vec_IntPush( p->vCutPairs, ((pCut->Num1 << 16) | pCut->Num0) );
        Vec_IntWriteEntry( p->vNodeCuts, Node, Vec_IntSize(p->vCutPairs) - Vec_IntEntry(p->vNodeStarts, Node) );
    }
    // check if the node is over the list
    if ( p->nNodeCuts == p->pParams->nKeepMax )
        p->nCutsLimit++;
    // set the list at the node
    Vec_PtrFillExtra( p->vCutsNew, Node + 1, NULL );
    assert( Cut_NodeReadCutsNew(p, Node) == NULL );
    Cut_NodeWriteCutsNew( p, Node, pList );
    // filter the cuts
//clk = clock();
//    if ( p->pParams->fFilter )
//        Cut_CutFilter( p, pList0 );
//p->timeFilter += clock() - clk;
    return pList;
}
 
/**Function*************************************************************

  Synopsis    [Computes the cuts by merging cuts at two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeDoComputeCuts( Cut_Man_t * p, Cut_List_t * pSuper, int Node, int fCompl0, int fCompl1, Cut_Cut_t * pList0, Cut_Cut_t * pList1, int fTriv )
{
    Cut_Cut_t * pStop0, * pStop1, * pTemp0, * pTemp1;
    int i, nCutsOld, Limit;
    // get the cut lists of children
    if ( pList0 == NULL || pList1 == NULL )
        return;
    // start the new list
    nCutsOld = p->nCutsCur;
    Limit = p->pParams->nVarsMax;
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
    if ( fTriv ) 
    {
        pTemp0 = Cut_CutCreateTriv( p, Node );
        Cut_ListAdd( pSuper, pTemp0 );
        p->nNodeCuts++;
        nCutsOld++;
    }
    // small by small
    Cut_ListForEachCutStop( pList0, pTemp0, pStop0 )
    Cut_ListForEachCutStop( pList1, pTemp1, pStop1 )
        if ( Cut_CutProcessTwo( p, pTemp0, pTemp1, pSuper ) )
            return;
    // small by large
    Cut_ListForEachCutStop( pList0, pTemp0, pStop0 )
    Cut_ListForEachCut( pStop1, pTemp1 )
    {
        if ( (pTemp0->uSign & pTemp1->uSign) != pTemp0->uSign )
            continue;
        if ( Cut_CutProcessTwo( p, pTemp0, pTemp1, pSuper ) )
            return;
    }
    // small by large
    Cut_ListForEachCutStop( pList1, pTemp1, pStop1 )
    Cut_ListForEachCut( pStop0, pTemp0 )
    {
        if ( (pTemp0->uSign & pTemp1->uSign) != pTemp1->uSign )
            continue;
        if ( Cut_CutProcessTwo( p, pTemp0, pTemp1, pSuper ) )
            return;
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
        if ( Cut_CutProcessTwo( p, pTemp0, pTemp1, pSuper ) )
            return;
    } 
    if ( fTriv ) 
    {
        p->nCutsMulti += p->nCutsCur - nCutsOld;         
        p->nNodesMulti++;
    }
}

/**Function*************************************************************

  Synopsis    [Computes the cuts by unioning cuts at a choice node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_NodeUnionCuts( Cut_Man_t * p, Vec_Int_t * vNodes )
{
    Cut_List_t Super, * pSuper = &Super;
    Cut_Cut_t * pList, * pListStart, * pCut, * pCut2, * pTop;
    int i, k, Node, Root, Limit = p->pParams->nVarsMax;
    int clk = clock();

    // start the new list
    Cut_ListStart( pSuper );

    // remember the root node to save the resulting cuts
    Root = Vec_IntEntry( vNodes, 0 );
    p->nNodeCuts = 1;

    // collect small cuts first
    Vec_PtrClear( p->vTemp );
    Vec_IntForEachEntry( vNodes, Node, i )
    {
        // get the cuts of this node
        pList = Cut_NodeReadCutsNew( p, Node );
        Cut_NodeWriteCutsNew( p, Node, NULL );
        assert( pList );
        // remember the starting point
        pListStart = pList->pNext;
        pList->pNext = NULL;
        // save or recycle the elementary cut
        if ( i == 0 )
            Cut_ListAdd( pSuper, pList ), pTop = pList;
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
            if ( p->pParams->fFilter && Cut_CutFilterOne( p, pSuper, pCut ) )
                continue;
            // set the complemented bit by comparing the first cut with the current cut
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            pListStart = pCut->pNext;
            pCut->pNext = NULL;
            // add to the list
            Cut_ListAdd( pSuper, pCut );
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
            if ( p->pParams->fFilter && Cut_CutFilterOne( p, pSuper, pCut ) )
                continue;
            // set the complemented bit
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            pListStart = pCut->pNext;
            pCut->pNext = NULL;
            // add to the list
            Cut_ListAdd( pSuper, pCut );
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
    assert( Cut_NodeReadCutsNew(p, Root) == NULL );
    pList = Cut_ListFinish( pSuper );
    Cut_NodeWriteCutsNew( p, Root, pList );
p->timeUnion += clock() - clk;
    // filter the cuts
//clk = clock();
//    if ( p->pParams->fFilter )
//        Cut_CutFilter( p, pList );
//p->timeFilter += clock() - clk;
    p->nNodes -= vNodes->nSize - 1;
    return pList;
}


/**Function*************************************************************

  Synopsis    [Verifies that the list contains only non-dominated cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_CutListVerify( Cut_Cut_t * pList )
{ 
    Cut_Cut_t * pCut, * pDom;
    Cut_ListForEachCut( pList, pCut )
    {
        Cut_ListForEachCutStop( pList, pDom, pCut )
        {
            if ( Cut_CutCheckDominance( pDom, pCut ) )
            {
                int x = 0;
                printf( "******************* These are contained cuts:\n" );
                Cut_CutPrint( pDom, 1 );
                Cut_CutPrint( pDom, 1 );
                
                return 0;
            }
        }
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


