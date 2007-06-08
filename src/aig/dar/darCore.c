/**CFile****************************************************************

  FileName    [darCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Core of the rewriting package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darCore.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManRewrite( Dar_Man_t * p )
{
    ProgressBar * pProgress;
    Dar_Obj_t * pObj, * pObjNew;
    int i, k, nNodesOld, nNodeBefore, nNodeAfter, Required;
    int clk = 0, clkStart = clock();
    // remove dangling nodes
    Dar_ManCleanup( p );
    // set elementary cuts for the PIs
    Dar_ManSetupPis( p );
//    if ( p->pPars->fUpdateLevel )
//        Dar_NtkStartReverseLevels( p );
    // resynthesize each node once
    nNodesOld = Vec_PtrSize( p->vObjs );
    pProgress = Extra_ProgressBarStart( stdout, nNodesOld );
    Dar_ManForEachObj( p, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( !Dar_ObjIsNode(pObj) )
            continue;
        if ( i > nNodesOld )
            break;
        // compute cuts for the node
        Dar_ObjComputeCuts_rec( p, pObj );
        // go through the cuts of this node
        Required = 1000000;
        p->GainBest = -1;
        for ( k = 1; k < (int)pObj->nCuts; k++ )
            Dar_LibEval( p, pObj, (Dar_Cut_t *)pObj->pData + k, Required );
        // check the best gain
        if ( !(p->GainBest > 0 || p->GainBest == 0 && p->pPars->fUseZeros) )
            continue;
        // if we end up here, a rewriting step is accepted
        nNodeBefore = Dar_ManNodeNum( p );
        pObjNew = Dar_LibBuildBest( p );
        pObjNew = Dar_NotCond( pObjNew, pObjNew->fPhase ^ pObj->fPhase );
        // remove the old nodes
        Dar_ObjReplace( p, pObj, pObjNew, 1 );
        // compare the gains
        nNodeAfter = Dar_ManNodeNum( p );
        assert( p->GainBest == nNodeBefore - nNodeAfter );
        assert( (int)pObjNew->Level <= Required );
    }
    Extra_ProgressBarStop( pProgress );
    Dar_ManCutsFree( p );
    // put the nodes into the DFS order and reassign their IDs
//    Dar_NtkReassignIds( p );

    // fix the levels
//    if ( p->pPars->fUpdateLevel )
//        Dar_NtkStopReverseLevels( p );
    // check
    if ( !Dar_ManCheck( p ) )
    {
        printf( "Dar_ManRewrite: The network check has failed.\n" );
        return 0;
    }
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


