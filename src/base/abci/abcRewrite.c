/**CFile****************************************************************

  FileName    [abcRewrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Technology-independent resynthesis of the AIG based on DAG aware rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRewrite.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "rwr.h"
#include "dec.h"

/*
    The ideas realized in this package are inspired by the paper:
    Per Bjesse, Arne Boralv, "DAG-aware circuit compression for 
    formal verification", Proc. ICCAD 2004, pp. 42-49.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Cut_Man_t * Abc_NtkStartCutManForRewrite( Abc_Ntk_t * pNtk, int fDrop );
static void        Abc_NodePrintCuts( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental rewriting of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRewrite( Abc_Ntk_t * pNtk, int fUseZeros, int fVerbose )
{
    int fDrop = 0;
    ProgressBar * pProgress;
    Cut_Man_t * pManCut;
    Rwr_Man_t * pManRwr;
    Abc_Obj_t * pNode;
    int i, nNodes, nGain;
    int clk, clkStart = clock();

    assert( Abc_NtkIsStrash(pNtk) );
    // cleanup the AIG
    Abc_AigCleanup(pNtk->pManFunc);
    // start the rewriting manager
    pManRwr = Rwr_ManStart( 0 );
    if ( pManRwr == NULL )
        return 0;
    Abc_NtkStartReverseLevels( pNtk );
    // start the cut manager
clk = clock();
    pManCut = Abc_NtkStartCutManForRewrite( pNtk, fDrop );
Rwr_ManAddTimeCuts( pManRwr, clock() - clk );
    pNtk->pManCut = pManCut;

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        // skip the constant node
        if ( Abc_NodeIsConst(pNode) )
            continue;
        // skip the nodes with many fanouts
        if ( Abc_ObjFanoutNum(pNode) > 1000 )
            continue;
        // for each cut, try to resynthesize it
        nGain = Rwr_NodeRewrite( pManRwr, pManCut, pNode, fUseZeros );
        if ( nGain > 0 || nGain == 0 && fUseZeros )
        {
            Dec_Graph_t * pGraph = Rwr_ManReadDecs(pManRwr);
            int fCompl           = Rwr_ManReadCompl(pManRwr);
            // complement the FF if needed
            if ( fCompl ) Dec_GraphComplement( pGraph );
            Dec_GraphUpdateNetwork( pNode, pGraph, nGain );
            if ( fCompl ) Dec_GraphComplement( pGraph );
        }
    }
    Extra_ProgressBarStop( pProgress );
Rwr_ManAddTimeTotal( pManRwr, clock() - clkStart );
    // print stats
    if ( fVerbose )
        Rwr_ManPrintStats( pManRwr );
    // delete the managers
    Rwr_ManStop( pManRwr );
    Cut_ManStop( pManCut );
    pNtk->pManCut = NULL;
    Abc_NtkStopReverseLevels( pNtk );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRewrite: The network check has failed.\n" );
        return 0;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Starts the cut manager for rewriting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Abc_NtkStartCutManForRewrite( Abc_Ntk_t * pNtk, int fDrop )
{
    static Cut_Params_t Params, * pParams = &Params;
    Cut_Man_t * pManCut;
    Abc_Obj_t * pObj;
    int i;
    // start the cut manager
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = 4;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 250;   // the max number of cuts kept at a node
    pParams->fTruth    = 1;     // compute truth tables
    pParams->fHash     = 1;     // hash cuts to detect unique
    pParams->fFilter   = 0;     // filter dominated cuts
    pParams->fSeq      = 0;     // compute sequential cuts
    pParams->fDrop     = fDrop; // drop cuts on the fly
    pParams->fVerbose  = 0;     // the verbosiness flag
    pParams->nIdsMax   = Abc_NtkObjNumMax( pNtk );
    pManCut = Cut_ManStart( pParams );
    if ( pParams->fDrop )
        Cut_ManSetFanoutCounts( pManCut, Abc_NtkFanoutCounts(pNtk) );
    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_ObjFanoutNum(pObj) > 0 )
            Cut_NodeSetTriv( pManCut, pObj->Id );
    return pManCut;
}

/**Function*************************************************************

  Synopsis    [Prints the cuts at the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintCuts( Abc_Obj_t * pNode )
{
    Cut_Cut_t * pCut;
    unsigned uTruth;
    printf( "\nNode %s\n", Abc_ObjName(pNode) );
    for ( pCut = (Cut_Cut_t *)pNode->pCopy; pCut; pCut = pCut->pNext )
    {
        uTruth = pCut->uTruth;
        Extra_PrintBinary( stdout, &uTruth, 16 ); 
        printf( "   " );
        Cut_CutPrint( pCut );   
        printf( "\n" );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


