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

static inline Cut_Cut_t * Cut_CutCreateTriv( Cut_Man_t * p, int Node );
static inline void        Cut_CutRecycle( Cut_Man_t * p, Cut_Cut_t * pCut );
static inline int         Cut_CutProcessTwo( Cut_Man_t * p, int Root, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1, Cut_List_t * pSuperList );

static void               Cut_CutPrintMerge( Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );
static void               Cut_CutFilter( Cut_Man_t * p, Cut_Cut_t * pList );

// iterator through all the cuts of the list
#define Cut_ListForEachCut( pList, pCut )                 \
    for ( pCut = pList;                                   \
          pCut;                                           \
          pCut = pCut->pNext )
#define Cut_ListForEachCutStop( pList, pCut, pStop )      \
    for ( pCut = pList;                                   \
          pCut != pStop;                                  \
          pCut = pCut->pNext )
#define Cut_ListForEachCutSafe( pList, pCut, pCut2 )      \
    for ( pCut = pList,                                   \
          pCut2 = pCut? pCut->pNext: NULL;                \
          pCut;                                           \
          pCut = pCut2,                                   \
          pCut2 = pCut? pCut->pNext: NULL )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the pointer to the linked list of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_NodeReadCuts( Cut_Man_t * p, int Node )
{
    if ( Node >= p->vCuts->nSize )
        return NULL;
    return Vec_PtrEntry( p->vCuts, Node );
}

/**Function*************************************************************

  Synopsis    [Returns the pointer to the linked list of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeWriteCuts( Cut_Man_t * p, int Node, Cut_Cut_t * pList )
{
    Vec_PtrWriteEntry( p->vCuts, Node, pList );
}

/**Function*************************************************************

  Synopsis    [Sets the trivial cut for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeSetTriv( Cut_Man_t * p, int Node )
{
    assert( Cut_NodeReadCuts(p, Node) == NULL );
    Cut_NodeWriteCuts( p, Node, Cut_CutCreateTriv(p, Node) );
}

/**Function*************************************************************

  Synopsis    [Deallocates the cuts at the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeFreeCuts( Cut_Man_t * p, int Node )
{
    Cut_Cut_t * pList, * pCut, * pCut2;
    pList = Cut_NodeReadCuts( p, Node );
    if ( pList == NULL )
        return;
    Cut_ListForEachCutSafe( pList, pCut, pCut2 )
        Cut_CutRecycle( p, pCut );
    Cut_NodeWriteCuts( p, Node, NULL );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeSetComputedAsNew( Cut_Man_t * p, int Node )
{
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
    p->nCutsNode = 1;
    // small by small
    Cut_ListForEachCutStop( pList0, pTemp0, pStop0 )
    Cut_ListForEachCutStop( pList1, pTemp1, pStop1 )
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    // all by large
    Cut_ListForEachCut( pList0, pTemp0 )
    Cut_ListForEachCut( pStop1, pTemp1 )
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    // all by large
    Cut_ListForEachCut( pList1, pTemp1 )
    Cut_ListForEachCut( pStop0, pTemp0 )
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    // large by large
    Cut_ListForEachCut( pStop0, pTemp0 )
    Cut_ListForEachCut( pStop1, pTemp1 )
    {
        assert( pTemp0->nLeaves == (unsigned)Limit && pTemp1->nLeaves == (unsigned)Limit );
        for ( i = 0; i < Limit; i++ )
            if ( pTemp0->pLeaves[i] != pTemp1->pLeaves[i] )
                break;
        if ( i < Limit )
            continue;
        if ( Cut_CutProcessTwo( p, Node, pTemp0, pTemp1, &SuperList ) )
            goto finish;
    }
finish :
    // set the list at the node
    Vec_PtrFillExtra( p->vCuts, Node + 1, NULL );
    assert( Cut_NodeReadCuts(p, Node) == NULL );
    pList0 = Cut_ListFinish( &SuperList );
    Cut_NodeWriteCuts( p, Node, pList0 );
    // clear the hash table
    if ( p->pParams->fHash && !p->pParams->fSeq )
        Cut_TableClear( p->tTable );
    // consider dropping the fanins cuts
    if ( p->pParams->fDrop )
    {
        Cut_NodeTryDroppingCuts( p, Node0 );
        Cut_NodeTryDroppingCuts( p, Node1 );
    }
p->timeMerge += clock() - clk;
    // filter the cuts
clk = clock();
    if ( p->pParams->fFilter )
        Cut_CutFilter( p, pList0 );
p->timeFilter += clock() - clk;
    p->nNodes++;
    return pList0;
}

/**Function*************************************************************

  Synopsis    [Processes two cuts.]

  Description [Returns 1 if the limit has been reached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_CutProcessTwo( Cut_Man_t * p, int Root, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1, Cut_List_t * pSuperList )
{
    Cut_Cut_t * pCut;
    // merge the cuts
    if ( pCut0->nLeaves >= pCut1->nLeaves )
        pCut = Cut_CutMergeTwo( p, pCut0, pCut1 );
    else
        pCut = Cut_CutMergeTwo( p, pCut1, pCut0 );
    if ( pCut == NULL )
        return 0;
    assert( pCut->nLeaves > 1 );
    // add the root if sequential
    if ( p->pParams->fSeq )
        pCut->pLeaves[pCut->nLeaves] = Root;
    // check the lookup table
    if ( p->pParams->fHash && Cut_TableLookup( p->tTable, pCut, !p->pParams->fSeq  ) )
    {
        Cut_CutRecycle( p, pCut );
        return 0;
    }
    // compute the truth table
    if ( p->pParams->fTruth )
        Cut_TruthCompute( p, pCut, pCut0, pCut1 );
    // add to the list
    Cut_ListAdd( pSuperList, pCut );
    // return status (0 if okay; 1 if exceeded the limit)
    return ++p->nCutsNode == p->pParams->nKeepMax;
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
    p->nCutsNode = 1;

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
            // check hash tables
            if ( p->pParams->fHash && Cut_TableLookup( p->tTable, pCut, !p->pParams->fSeq ) )
            {
                Cut_CutRecycle( p, pCut );
                continue;
            }
            // set the complemented bit by comparing the first cut with the current cut
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            // add to the list
            Cut_ListAdd( &SuperList, pCut );
            if ( ++p->nCutsNode == p->pParams->nKeepMax )
            {
                // recycle the rest of the cuts of this node
                Cut_ListForEachCutSafe( pCut->pNext, pCut, pCut2 )
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
            if ( p->pParams->fHash && Cut_TableLookup( p->tTable, pCut, !p->pParams->fSeq  ) )
            {
                Cut_CutRecycle( p, pCut );
                continue;
            }
            // set the complemented bit
            pCut->fCompl = pTop->fSimul ^ pCut->fSimul;
            // add to the list
            Cut_ListAdd( &SuperList, pCut );
            if ( ++p->nCutsNode == p->pParams->nKeepMax )
            {
                // recycle the rest of the cuts
                Cut_ListForEachCutSafe( pCut->pNext, pCut, pCut2 )
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
    // clear the hash table
    if ( p->pParams->fHash && !p->pParams->fSeq )
        Cut_TableClear( p->tTable );
p->timeUnion += clock() - clk;
    // filter the cuts
clk = clock();
    if ( p->pParams->fFilter )
        Cut_CutFilter( p, pList );
p->timeFilter += clock() - clk;
    p->nNodes -= vNodes->nSize - 1;
    return pList;
}

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_CutAlloc( Cut_Man_t * p )
{
    Cut_Cut_t * pCut;
    // cut allocation
    pCut = (Cut_Cut_t *)Extra_MmFixedEntryFetch( p->pMmCuts );
    memset( pCut, 0, sizeof(Cut_Cut_t) );
    pCut->nVarsMax   = p->pParams->nVarsMax;
    pCut->fSeq       = p->pParams->fSeq;
    pCut->fSimul     = p->fSimul;
    // statistics
    p->nCutsAlloc++;
    p->nCutsCur++;
    if ( p->nCutsPeak < p->nCutsAlloc - p->nCutsDealloc )
        p->nCutsPeak = p->nCutsAlloc - p->nCutsDealloc;
    return pCut;
}

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Cut_t * Cut_CutCreateTriv( Cut_Man_t * p, int Node )
{
    Cut_Cut_t * pCut;
    pCut = Cut_CutAlloc( p );
    pCut->nLeaves = 1;
    pCut->pLeaves[0] = Node;
    if ( p->pParams->fTruth )
        Cut_CutWriteTruth( pCut, p->uTruthVars[0] );
    p->nCutsTriv++;
    return pCut;
} 

/**Function*************************************************************

  Synopsis    [Start the cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_CutRecycle( Cut_Man_t * p, Cut_Cut_t * pCut )
{
    p->nCutsDealloc++;
    p->nCutsCur--;
    if ( pCut->nLeaves == 1 )
        p->nCutsTriv--;
    Extra_MmFixedEntryRecycle( p->pMmCuts, (char *)pCut );
}


/**Function*************************************************************

  Synopsis    [Consider dropping cuts if they are useless by now.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeTryDroppingCuts( Cut_Man_t * p, int Node )
{
    int nFanouts;
    assert( p->vFanCounts );
    nFanouts = Vec_IntEntry( p->vFanCounts, Node );
    assert( nFanouts > 0 );
    if ( --nFanouts == 0 )
        Cut_NodeFreeCuts( p, Node );
    Vec_IntWriteEntry( p->vFanCounts, Node, nFanouts );
}

/**Function*************************************************************

  Synopsis    [Print the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_CutPrint( Cut_Cut_t * pCut )
{
    int i;
    assert( pCut->nLeaves > 0 );
    printf( "%d : {", pCut->nLeaves );
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        printf( " %d", pCut->pLeaves[i] );
    printf( " }" );
}

/**Function*************************************************************

  Synopsis    [Consider dropping cuts if they are useless by now.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_CutPrintMerge( Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
    printf( "\n" );
    printf( "%d : %5d %5d %5d %5d %5d\n", 
        pCut0->nLeaves, 
        pCut0->nLeaves > 0 ? pCut0->pLeaves[0] : -1, 
        pCut0->nLeaves > 1 ? pCut0->pLeaves[1] : -1, 
        pCut0->nLeaves > 2 ? pCut0->pLeaves[2] : -1, 
        pCut0->nLeaves > 3 ? pCut0->pLeaves[3] : -1, 
        pCut0->nLeaves > 4 ? pCut0->pLeaves[4] : -1
        );
    printf( "%d : %5d %5d %5d %5d %5d\n", 
        pCut1->nLeaves, 
        pCut1->nLeaves > 0 ? pCut1->pLeaves[0] : -1, 
        pCut1->nLeaves > 1 ? pCut1->pLeaves[1] : -1, 
        pCut1->nLeaves > 2 ? pCut1->pLeaves[2] : -1, 
        pCut1->nLeaves > 3 ? pCut1->pLeaves[3] : -1, 
        pCut1->nLeaves > 4 ? pCut1->pLeaves[4] : -1
        );
    if ( pCut == NULL )
        printf( "Cannot merge\n" );
    else
        printf( "%d : %5d %5d %5d %5d %5d\n", 
            pCut->nLeaves, 
            pCut->nLeaves > 0 ? pCut->pLeaves[0] : -1, 
            pCut->nLeaves > 1 ? pCut->pLeaves[1] : -1, 
            pCut->nLeaves > 2 ? pCut->pLeaves[2] : -1, 
            pCut->nLeaves > 3 ? pCut->pLeaves[3] : -1, 
            pCut->nLeaves > 4 ? pCut->pLeaves[4] : -1
            );
}


/**Function*************************************************************

  Synopsis    [Filter the cuts using dominance.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_CutFilter( Cut_Man_t * p, Cut_Cut_t * pList )
{ 
    Cut_Cut_t * pListR, ** ppListR = &pListR;
    Cut_Cut_t * pCut, * pCut2, * pDom, * pPrev;
    int i, k;
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
            if ( pDom->nLeaves >= pCut->nLeaves )
                continue;
            // check if every node in pDom is contained in pCut
            for ( i = 0; i < (int)pDom->nLeaves; i++ )
            {
                for ( k = 0; k < (int)pCut->nLeaves; k++ )
                    if ( pDom->pLeaves[i] == pCut->pLeaves[k] )
                        break;
                if ( k == (int)pCut->nLeaves ) // node i in pDom is not contained in pCut
                    break;
            }
            if ( i == (int)pDom->nLeaves ) // every node in pDom is contained in pCut
                break;
        }
        if ( pDom != pCut ) // pDom is contained in pCut - recycle pCut
        {
            // make sure cuts are connected after removing
            pPrev->pNext = pCut->pNext;
/*
            // report
            printf( "Recycling cut:   " );
            Cut_CutPrint( pCut );
            printf( "\n" );
            printf( "As contained in: " );
            Cut_CutPrint( pDom );
            printf( "\n" );
*/
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



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


