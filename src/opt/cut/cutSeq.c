/**CFile****************************************************************

  FileName    [cutSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Sequential cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Cut_NodeShiftLat( Cut_Man_t * p, int Node, int nLat );
static int  Cut_ListCount( Cut_Cut_t * pList );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes sequential cuts for the node from its fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeComputeCutsSeq( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1, int nLat0, int nLat1, int fTriv, int CutSetNum )
{
    Cut_List_t List1, List2, List3;
    Cut_Cut_t * pList1, * pList2, * pList3, * pListNew;
    int clk = clock();

//    assert( Node != Node0 );
//    assert( Node != Node1 );

    // get the number of cuts at the node
    p->nNodeCuts = Cut_ListCount( Cut_NodeReadCutsOld(p, Node) );
    if ( p->nNodeCuts >= p->pParams->nKeepMax )
        return;
    // count only the first visit
    if ( p->nNodeCuts == 0 )
        p->nNodes++;

    // shift the cuts by as many latches
    if ( nLat0 ) Cut_NodeShiftLat( p, Node0, nLat0 );
    if ( nLat1 ) Cut_NodeShiftLat( p, Node1, nLat1 );

    // merge the old and new
    pList1 = Cut_NodeDoComputeCuts( p, Node, Node0, Node1, fCompl0, fCompl1, 0, 1, 0 );
    // merge the new and old
    pList2 = Cut_NodeDoComputeCuts( p, Node, Node0, Node1, fCompl0, fCompl1, 1, 0, 0 );
    // merge the new and new
    pList3 = Cut_NodeDoComputeCuts( p, Node, Node0, Node1, fCompl0, fCompl1, 1, 1, fTriv );
p->timeMerge += clock() - clk;

    // merge all lists
    Cut_ListDerive( &List1, pList1 );
    Cut_ListDerive( &List2, pList2 );
    Cut_ListDerive( &List3, pList3 );
    Cut_ListAddList( &List1, &List2 );
    Cut_ListAddList( &List1, &List3 );

    // set the lists at the node
    pListNew = Cut_ListFinish( &List1 );
    if ( CutSetNum >= 0 )
    {
        assert( Cut_NodeReadCutsTemp(p, CutSetNum) == NULL );
        Cut_NodeWriteCutsTemp( p, CutSetNum, pListNew );
    }
    else
    {
        assert( Cut_NodeReadCutsNew(p, Node) == NULL );
        Cut_NodeWriteCutsNew( p, Node, pListNew );
    }

    // shift the cuts by as many latches back
    if ( nLat0 ) Cut_NodeShiftLat( p, Node0, -nLat0 );
    if ( nLat1 ) Cut_NodeShiftLat( p, Node1, -nLat1 );

    if ( p->nNodeCuts >= p->pParams->nKeepMax )
        p->nCutsLimit++;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeNewMergeWithOld( Cut_Man_t * p, int Node )
{
    Cut_List_t Old, New;
    Cut_Cut_t * pListOld, * pListNew;
    // get the new cuts
    pListNew = Cut_NodeReadCutsNew( p, Node );
    if ( pListNew == NULL )
        return;
    Cut_NodeWriteCutsNew( p, Node, NULL );
    // get the old cuts
    pListOld = Cut_NodeReadCutsOld( p, Node );
    if ( pListOld == NULL )
    {
        Cut_NodeWriteCutsOld( p, Node, pListNew );
        return;
    }
    // merge the lists
    Cut_ListDerive( &Old, pListOld );
    Cut_ListDerive( &New, pListNew );
    Cut_ListAddList( &Old, &New );
    pListOld = Cut_ListFinish( &Old );
    Cut_NodeWriteCutsOld( p, Node, pListOld );
}


/**Function*************************************************************

  Synopsis    [Returns 1 if something was transferred.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_NodeTempTransferToNew( Cut_Man_t * p, int Node, int CutSetNum )
{
    Cut_Cut_t * pCut;
    pCut = Cut_NodeReadCutsTemp( p, CutSetNum );
    Cut_NodeWriteCutsTemp( p, CutSetNum, NULL );
    Cut_NodeWriteCutsNew( p, Node, pCut );
    return pCut != NULL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if something was transferred.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeOldTransferToNew( Cut_Man_t * p, int Node )
{
    Cut_Cut_t * pCut;
    pCut = Cut_NodeReadCutsOld( p, Node );
    Cut_NodeWriteCutsOld( p, Node, NULL );
    Cut_NodeWriteCutsNew( p, Node, pCut );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_NodeShiftLat( Cut_Man_t * p, int Node, int nLat )
{
    Cut_Cut_t * pTemp;
    int i;
    // shift the cuts by as many latches
    Cut_ListForEachCut( Cut_NodeReadCutsOld(p, Node), pTemp )
    {
        pTemp->uSign = 0;
        for ( i = 0; i < (int)pTemp->nLeaves; i++ )
        {
            pTemp->pLeaves[i] += nLat;
            pTemp->uSign      |= Cut_NodeSign( pTemp->pLeaves[i] );
        }
    }
    Cut_ListForEachCut( Cut_NodeReadCutsNew(p, Node), pTemp )
    {
        pTemp->uSign = 0;
        for ( i = 0; i < (int)pTemp->nLeaves; i++ )
        {
            pTemp->pLeaves[i] += nLat;
            pTemp->uSign      |= Cut_NodeSign( pTemp->pLeaves[i] );
        }
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_ListCount( Cut_Cut_t * pList )
{
    int Counter = 0;
    Cut_ListForEachCut( pList, pList )
        Counter++;
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


