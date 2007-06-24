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
    Dar_Cut_t * pCutSet;
    Dar_Obj_t * pObj, * pObjNew;
    int i, k, nNodesOld, nNodeBefore, nNodeAfter, Required;
    int clk = 0, clkStart;
    // remove dangling nodes
    Dar_ManCleanup( p );
    // set elementary cuts for the PIs
    Dar_ManSetupPis( p );
//    if ( p->pPars->fUpdateLevel )
//        Dar_NtkStartReverseLevels( p );
    // resynthesize each node once
    clkStart = clock();
    p->nNodesInit = Dar_ManNodeNum(p);
    nNodesOld = Vec_PtrSize( p->vObjs );
    pProgress = Extra_ProgressBarStart( stdout, nNodesOld );
    Dar_ManForEachObj( p, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( !Dar_ObjIsNode(pObj) )
            continue;
        if ( i > nNodesOld )
            break;
        if ( pObj->Id == 654 )
        {
            int x = 0;
        }
        // compute cuts for the node
clk = clock();
        pCutSet = Dar_ObjComputeCuts_rec( p, pObj );
p->timeCuts += clock() - clk;
        // go through the cuts of this node
        Required = 1000000;
        p->GainBest = -1;
        for ( k = 1; k < (int)pObj->nCuts; k++ )
        {
/*
            if ( pObj->Id == 654 )
            {
                int m;
                for ( m = 0; m < 4; m++ )
                    printf( "%d ", pCutSet[k].pLeaves[m] );
                printf( "\n" );
            }
*/
            Dar_LibEval( p, pObj, pCutSet + k, Required );
        }
        // check the best gain
        if ( !(p->GainBest > 0 || p->GainBest == 0 && p->pPars->fUseZeros) )
            continue;
        // if we end up here, a rewriting step is accepted
        nNodeBefore = Dar_ManNodeNum( p );
        pObjNew = Dar_LibBuildBest( p );
        pObjNew = Dar_NotCond( pObjNew, pObjNew->fPhase ^ pObj->fPhase );
        assert( (int)Dar_Regular(pObjNew)->Level <= Required );
        // replace the node
        Dar_ObjReplace( p, pObj, pObjNew, 1 );
        // remove the old cuts
        pObj->pData = NULL;
        // compare the gains
        nNodeAfter = Dar_ManNodeNum( p );
        assert( p->GainBest <= nNodeBefore - nNodeAfter );
        // count gains of this class
        p->ClassGains[p->ClassBest] += nNodeBefore - nNodeAfter;

    }
p->timeTotal = clock() - clkStart;
p->timeOther = p->timeTotal - p->timeCuts - p->timeEval;

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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManComputeCuts( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i, clk = 0, clkStart = clock();
    int nCutsMax = 0, nCutsTotal = 0;
    // remove dangling nodes
    Dar_ManCleanup( p );
    // set elementary cuts for the PIs
    Dar_ManSetupPis( p );
    // compute cuts for each nodes in the topological order
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) )
            continue;
        Dar_ObjComputeCuts( p, pObj );
        nCutsTotal += pObj->nCuts - 1;
        nCutsMax = DAR_MAX( nCutsMax, (int)pObj->nCuts - 1 );
    }
    // print statistics on the number of non-trivial cuts
    printf( "Node = %6d. Cut = %8d. Max = %3d. Ave = %.2f.  Filter = %8d. Created = %8d.\n", 
        Dar_ManNodeNum(p), nCutsTotal, nCutsMax, (float)nCutsTotal/Dar_ManNodeNum(p), 
        p->nCutsFiltered, p->nCutsFiltered+nCutsTotal+Dar_ManNodeNum(p)+Dar_ManPiNum(p) );
    PRT( "Time", clock() - clkStart );

    // free the cuts
//    Dar_ManCutsFree( p );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


