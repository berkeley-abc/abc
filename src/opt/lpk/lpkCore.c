/**CFile****************************************************************

  FileName    [lpkCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: lpkCore.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lpkInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if at least one entry has changed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_NodeHasChanged( Lpk_Man_t * p, int iNode )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pTemp;
    int i;
    vNodes = Vec_VecEntry( p->vVisited, iNode );
    if ( Vec_PtrSize(vNodes) == 0 )
        return 1;
    Vec_PtrForEachEntry( vNodes, pTemp, i )
    {
        // check if the node has changed
        pTemp = Abc_NtkObj( p->pNtk, (int)pTemp );
        if ( pTemp == NULL )
            return 1;
        // check if the number of fanouts has changed
//        if ( Abc_ObjFanoutNum(pTemp) != (int)Vec_PtrEntry(vNodes, i+1) )
//            return 1;
        i++;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resynthesis for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_ResynthesizeNode( Lpk_Man_t * p )
{
    Kit_DsdNtk_t * pDsdNtk;
    Lpk_Cut_t * pCut;
    unsigned * pTruth;
    void * pDsd = NULL;
    int i, RetValue, clk;

    Lpk_Cut_t * pCutMax;

    // compute the cuts
clk = clock();
    if ( !Lpk_NodeCuts( p ) )
    {
p->timeCuts += clock() - clk;
        return 0;
    }
p->timeCuts += clock() - clk;

    // find the max volume cut
    pCutMax = NULL;
    for ( i = 0; i < p->nEvals; i++ )
    {
        pCut = p->pCuts + p->pEvals[i];
        if ( pCutMax == NULL || pCutMax->nNodes < pCut->nNodes )
            pCutMax = pCut;
    }
    assert( pCutMax != NULL );
    

    if ( p->pPars->fVeryVerbose )
    printf( "Node %5d : Mffc size = %5d. Cuts = %5d.\n", p->pObj->Id, p->nMffc, p->nEvals );
    // try the good cuts
    p->nCutsTotal  += p->nCuts;
    p->nCutsUseful += p->nEvals;
    for ( i = 0; i < p->nEvals; i++ )
    {
        // get the cut
        pCut = p->pCuts + p->pEvals[i];

        if ( pCut != pCutMax )
            continue;

        // compute the truth table
clk = clock();
        pTruth = Lpk_CutTruth( p, pCut );
p->timeTruth += clock() - clk;

clk = clock();
        pDsdNtk = Kit_DsdDeriveNtk( pTruth, pCut->nLeaves, p->pPars->nLutSize );
p->timeEval += clock() - clk;

        if ( Kit_DsdNtkRoot(pDsdNtk)->nFans == 16 ) // skip 16-input non-DSD because ISOP will not work
        {
            Kit_DsdNtkFree( pDsdNtk );
            continue;
        }

        if ( p->pPars->fVeryVerbose )
        {
            printf( "  C%02d: L= %2d/%2d  V= %2d/%d  N= %d  W= %4.2f  ", 
                i, pCut->nLeaves, Extra_TruthSupportSize(pTruth, pCut->nLeaves), pCut->nNodes, pCut->nNodesDup, pCut->nLuts, pCut->Weight );
            Kit_DsdPrint( stdout, pDsdNtk );
        }

        // update the network
clk = clock();
        RetValue = Lpk_CutExplore( p, pCut, pDsdNtk );
        Kit_DsdNtkFree( pDsdNtk );
p->timeMap += clock() - clk;
        if ( RetValue )
            break;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs resynthesis for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_Resynthesize( Abc_Ntk_t * pNtk, Lpk_Par_t * pPars )
{
    ProgressBar * pProgress;
    Lpk_Man_t * p;
    Abc_Obj_t * pObj;
    double Delta;
    int i, Iter, nNodes, nNodesPrev, clk = clock();
    assert( Abc_NtkIsLogic(pNtk) );

    // get the number of inputs
    pPars->nLutSize = Abc_NtkGetFaninMax( pNtk );
    // adjust the number of crossbars based on LUT size
    if ( pPars->nVarsShared > pPars->nLutSize - 2 )
        pPars->nVarsShared = pPars->nLutSize - 2;
    // get the max number of LUTs tried
    pPars->nVarsMax = pPars->nLutsMax * (pPars->nLutSize - 1) + 1; // V = N * (K-1) + 1
    while ( pPars->nVarsMax > 16 )
    {
        pPars->nLutsMax--;
        pPars->nVarsMax = pPars->nLutsMax * (pPars->nLutSize - 1) + 1;

    }
    if ( pPars->fVerbose )
    {
        printf( "Resynthesis for %d %d-LUTs with %d non-MFFC LUTs, %d crossbars, and %d-input cuts.\n",
            pPars->nLutsMax, pPars->nLutSize, pPars->nLutsOver, pPars->nVarsShared, pPars->nVarsMax );
    }
 
    // convert logic to AIGs
    Abc_NtkToAig( pNtk );

    // start the manager
    p = Lpk_ManStart( pPars );
    p->pNtk = pNtk;
    p->nNodesTotal = Abc_NtkNodeNum(pNtk);
    p->vLevels = Vec_VecStart( 3 * Abc_NtkLevel(pNtk) ); // computes levels of all nodes
    if ( p->pPars->fSatur )
        p->vVisited = Vec_VecStart( 0 );

    // iterate over the network
    nNodesPrev = p->nNodesTotal;
    for ( Iter = 1; ; Iter++ )
    {
        // expand storage for changed nodes
        if ( p->pPars->fSatur )
            Vec_VecExpand( p->vVisited, Abc_NtkObjNumMax(pNtk) + 1 );

        // consider all nodes
        nNodes = Abc_NtkObjNumMax(pNtk);
        if ( !pPars->fVeryVerbose )
            pProgress = Extra_ProgressBarStart( stdout, nNodes );
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            // skip all except the final node
//            if ( !Abc_ObjIsCo(Abc_ObjFanout0(pObj)) )
//                continue;

            if ( i >= nNodes )
                break;
            if ( !pPars->fVeryVerbose )
                Extra_ProgressBarUpdate( pProgress, i, NULL );
            // skip the nodes that did not change
            if ( p->pPars->fSatur && !Lpk_NodeHasChanged(p, pObj->Id) )
                continue;
            // resynthesize
            p->pObj = pObj;
            Lpk_ResynthesizeNode( p );

            if ( p->nChanges == 3 )
                break;
        }
        if ( !pPars->fVeryVerbose )
            Extra_ProgressBarStop( pProgress );

        // check the increase
        Delta = 100.00 * (nNodesPrev - Abc_NtkNodeNum(pNtk)) / p->nNodesTotal;
        if ( Delta < 0.05 )
            break;
        nNodesPrev = Abc_NtkNodeNum(pNtk);
        if ( !p->pPars->fSatur )
            break;

        break;
    }

    if ( pPars->fVerbose )
    {
        printf( "N = %5d (%3d)  Cut = %5d (%4d)  Change = %5d  Gain = %5d  (%5.2f %%) Iter = %2d\n", 
            p->nNodesTotal, p->nNodesOver, p->nCutsTotal, p->nCutsUseful, p->nChanges, p->nGainTotal, 100.0 * p->nGainTotal / p->nNodesTotal, Iter );
        printf( "Non_DSD blocks: " );
        for ( i = 3; i <= pPars->nVarsMax; i++ )
            if ( p->nBlocks[i] )
                printf( "%d=%d  ", i, p->nBlocks[i] );
        printf( "\n" );
        p->timeTotal = clock() - clk;
        p->timeOther = p->timeTotal - p->timeCuts - p->timeTruth - p->timeEval - p->timeMap;
        PRTP( "Cuts  ", p->timeCuts,  p->timeTotal );
        PRTP( "Truth ", p->timeTruth, p->timeTotal );
        PRTP( "Eval  ", p->timeEval,  p->timeTotal );
        PRTP( "Map   ", p->timeMap,   p->timeTotal );
        PRTP( "Other ", p->timeOther, p->timeTotal );
        PRTP( "TOTAL ", p->timeTotal, p->timeTotal );
    }

    Lpk_ManStop( p );
    // check the resulting network
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Lpk_Resynthesize: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


