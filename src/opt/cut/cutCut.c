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
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

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
    pCut->nLeaves    = 1;
    pCut->pLeaves[0] = Node;
    pCut->uSign      = (1 << (Node % 32));
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


