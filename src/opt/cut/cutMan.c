/**CFile****************************************************************

  FileName    [cutMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Cut manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the cut manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Cut_ManStart( Cut_Params_t * pParams )
{
    Cut_Man_t * p;
    int clk = clock();
    assert( pParams->nVarsMax >= 4 && pParams->nVarsMax <= 6 );
    p = ALLOC( Cut_Man_t, 1 );
    memset( p, 0, sizeof(Cut_Man_t) );
    // set and correct parameters
    p->pParams = pParams;
    if ( p->pParams->fSeq )
        p->pParams->fHash = 1;
    // space for cuts
    p->vCuts = Vec_PtrAlloc( pParams->nIdsMax );
    Vec_PtrFill( p->vCuts, pParams->nIdsMax, NULL );
    if ( pParams->fSeq )
    {
        p->vCutsNew = Vec_PtrAlloc( pParams->nIdsMax );
        Vec_PtrFill( p->vCuts, pParams->nIdsMax, NULL );
    }
    // hash tables
    if ( pParams->fHash )
        p->tTable = Cut_TableStart( p->pParams->nKeepMax );
    // entry size
    p->EntrySize = sizeof(Cut_Cut_t) + (pParams->nVarsMax + pParams->fSeq) * sizeof(int);
    if ( pParams->nVarsMax == 5 )
        p->EntrySize += sizeof(unsigned);
    else if ( pParams->nVarsMax == 6 )
        p->EntrySize += 2 * sizeof(unsigned);
    // memory for cuts
    p->pMmCuts = Extra_MmFixedStart( p->EntrySize );
    // precomputations
//    if ( pParams->fTruth && pParams->nVarsMax == 4 )
//        p->pPerms43 = Extra_TruthPerm43();
//    else if ( pParams->fTruth )
//    {
//        p->pPerms53 = Extra_TruthPerm53();
//        p->pPerms54 = Extra_TruthPerm54();
//    }
    p->uTruthVars[0][1] = p->uTruthVars[0][0] = 0xAAAAAAAA;    // 1010 1010 1010 1010 1010 1010 1010 1010
    p->uTruthVars[1][1] = p->uTruthVars[1][0] = 0xCCCCCCCC;    // 1010 1010 1010 1010 1010 1010 1010 1010
    p->uTruthVars[2][1] = p->uTruthVars[2][0] = 0xF0F0F0F0;    // 1111 0000 1111 0000 1111 0000 1111 0000
    p->uTruthVars[3][1] = p->uTruthVars[3][0] = 0xFF00FF00;    // 1111 1111 0000 0000 1111 1111 0000 0000
    p->uTruthVars[4][1] = p->uTruthVars[4][0] = 0xFFFF0000;    // 1111 1111 1111 1111 0000 0000 0000 0000
    p->uTruthVars[5][0] = 0x00000000;
    p->uTruthVars[5][1] = 0xFFFFFFFF;
    p->vTemp = Vec_PtrAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the cut manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_ManStop( Cut_Man_t * p )
{
    Cut_Cut_t * pCut;
    int i;
    Vec_PtrForEachEntry( p->vCuts, pCut, i )
    {
        if ( pCut != NULL )
        {
            int k = 0;
        }
    }

    if ( p->vCutsNew )   Vec_PtrFree( p->vCutsNew );
    if ( p->vCuts )      Vec_PtrFree( p->vCuts );
    if ( p->vFanCounts ) Vec_IntFree( p->vFanCounts );
    if ( p->pPerms43 )   free( p->pPerms43 );
    if ( p->pPerms53 )   free( p->pPerms53 );
    if ( p->pPerms54 )   free( p->pPerms54 );
    if ( p->vTemp )      Vec_PtrFree( p->vTemp );
    if ( p->tTable )     Cut_TableStop( p->tTable );
    Extra_MmFixedStop( p->pMmCuts, 0 );
    free( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_ManPrintStats( Cut_Man_t * p )
{
    printf( "Cut computation statistics:\n" );
    printf( "Current cuts      = %8d. (Trivial = %d.)\n", p->nCutsCur-p->nCutsTriv, p->nCutsTriv );
    printf( "Peak cuts         = %8d.\n", p->nCutsPeak );
    printf( "Total allocated   = %8d.\n", p->nCutsAlloc );
    printf( "Total deallocated = %8d.\n", p->nCutsDealloc );
    printf( "Cuts per node     = %8.1f\n", ((float)(p->nCutsCur-p->nCutsTriv))/p->nNodes );
    printf( "The cut size      = %8d bytes.\n", p->EntrySize );
    printf( "Peak memory       = %8.2f Mb.\n", (float)p->nCutsPeak * p->EntrySize / (1<<20) );
    PRT( "Merge ", p->timeMerge );
    PRT( "Union ", p->timeUnion );
    PRT( "Hash  ", Cut_TableReadTime(p->tTable) );
    PRT( "Filter", p->timeFilter );
    PRT( "Truth ", p->timeTruth );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_ManSetFanoutCounts( Cut_Man_t * p, Vec_Int_t * vFanCounts )
{
    p->vFanCounts = vFanCounts;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


