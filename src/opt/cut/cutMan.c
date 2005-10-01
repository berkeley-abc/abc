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

extern void Npn_StartTruth8( uint8 uTruths[][32] );

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
    assert( pParams->nVarsMax >= 4 && pParams->nVarsMax <= CUT_SIZE_MAX );
    p = ALLOC( Cut_Man_t, 1 );
    memset( p, 0, sizeof(Cut_Man_t) );
    // set and correct parameters
    p->pParams = pParams;
    // prepare storage for cuts
    p->vCutsNew = Vec_PtrAlloc( pParams->nIdsMax );
    Vec_PtrFill( p->vCutsNew, pParams->nIdsMax, NULL );
    // prepare storage for sequential cuts
    if ( pParams->fSeq )
    {
        p->pParams->fFilter = 1;
        p->vCutsOld = Vec_PtrAlloc( pParams->nIdsMax );
        Vec_PtrFill( p->vCutsOld, pParams->nIdsMax, NULL );
        p->vCutsTemp = Vec_PtrAlloc( pParams->nCutSet );
        Vec_PtrFill( p->vCutsTemp, pParams->nCutSet, NULL );
    }
    assert( !pParams->fTruth || pParams->nVarsMax <= 5 );
    // entry size
    p->EntrySize = sizeof(Cut_Cut_t) + pParams->nVarsMax * sizeof(int);
    if ( pParams->fTruth && pParams->nVarsMax >= 5 && pParams->nVarsMax <= 8 )
        p->EntrySize += (1 << (pParams->nVarsMax - 5)) * sizeof(unsigned);
    // memory for cuts
    p->pMmCuts = Extra_MmFixedStart( p->EntrySize );
    // elementary truth tables
    Npn_StartTruth8( p->uTruths );
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
    Vec_PtrForEachEntry( p->vCutsNew, pCut, i )
        if ( pCut != NULL )
        {
            int k = 0;
        }
    if ( p->vCutsNew )   Vec_PtrFree( p->vCutsNew );
    if ( p->vCutsOld )   Vec_PtrFree( p->vCutsOld );
    if ( p->vCutsTemp )  Vec_PtrFree( p->vCutsTemp );
    if ( p->vFanCounts ) Vec_IntFree( p->vFanCounts );
    if ( p->pPerms43 )   free( p->pPerms43 );
    if ( p->pPerms53 )   free( p->pPerms53 );
    if ( p->pPerms54 )   free( p->pPerms54 );
    if ( p->vTemp )      Vec_PtrFree( p->vTemp );
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
    if ( p->pReady )
    {
        Cut_CutRecycle( p, p->pReady );
        p->pReady = NULL;
    }
    printf( "Cut computation statistics:\n" );
    printf( "Current cuts      = %8d. (Trivial = %d.)\n", p->nCutsCur-p->nCutsTriv, p->nCutsTriv );
    printf( "Peak cuts         = %8d.\n", p->nCutsPeak );
    printf( "Total allocated   = %8d.\n", p->nCutsAlloc );
    printf( "Total deallocated = %8d.\n", p->nCutsDealloc );
    printf( "Cuts filtered     = %8d.\n", p->nCutsFilter );
    printf( "Nodes saturated   = %8d. (Max cuts = %d.)\n", p->nCutsLimit, p->pParams->nKeepMax );
    printf( "Cuts per node     = %8.1f\n", ((float)(p->nCutsCur-p->nCutsTriv))/p->nNodes );
    printf( "The cut size      = %8d bytes.\n", p->EntrySize );
    printf( "Peak memory       = %8.2f Mb.\n", (float)p->nCutsPeak * p->EntrySize / (1<<20) );
    PRT( "Merge ", p->timeMerge );
    PRT( "Union ", p->timeUnion );
    PRT( "Filter", p->timeFilter );
    PRT( "Truth ", p->timeTruth );
    printf( "Nodes = %d. Multi = %d.  Cuts = %d. Multi = %d.\n", 
        p->nNodes, p->nNodesMulti, p->nCutsCur-p->nCutsTriv, p->nCutsMulti );
}

    
/**Function*************************************************************

  Synopsis    [Prints some interesting stats.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_ManPrintStatsToFile( Cut_Man_t * p, char * pFileName, int TimeTotal )
{
    FILE * pTable;
    pTable = fopen( "cut_stats.txt", "a+" );
    fprintf( pTable, "%-20s ", pFileName );
    fprintf( pTable, "%8d ", p->nNodes );
    fprintf( pTable, "%6.1f ", ((float)(p->nCutsCur))/p->nNodes );
    fprintf( pTable, "%6.2f ", ((float)(100.0 * p->nCutsLimit))/p->nNodes );
    fprintf( pTable, "%6.2f ", (float)p->nCutsPeak * p->EntrySize / (1<<20) );
    fprintf( pTable, "%6.2f ", (float)(TimeTotal)/(float)(CLOCKS_PER_SEC) );
    fprintf( pTable, "\n" );
    fclose( pTable );
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_ManReadVarsMax( Cut_Man_t * p )
{
    return p->pParams->nVarsMax;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


