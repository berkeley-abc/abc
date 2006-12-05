/**CFile****************************************************************

  FileName    [ifSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Sequential mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifSeq.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void If_ObjPerformMappingLI( If_Man_t * p, If_Obj_t * pLatch );
static void If_ObjPerformMappingLO( If_Man_t * p, If_Obj_t * pLatch, If_Obj_t * pObj );
static int  If_ManMappingSeqConverged( If_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingSeq( If_Man_t * p )
{
    If_Obj_t * pObj, * pLatch;
    int i, clkTotal = clock();
    // set the number of cuts used
    p->nCutsUsed = p->pPars->nCutsMax;
    // set arrival times and trivial cuts at const 1 and PIs
    If_ManConst1(p)->Cuts[0].Delay = 0.0;
    If_ManForEachPi( p, pObj, i )
        pObj->Cuts[0].Delay = p->pPars->pTimesArr[i];
    // set the fanout estimates of the PIs
    If_ManForEachPi( p, pObj, i )
        pObj->EstRefs = (float)1.0;
    // delay oriented mapping
    p->pPars->fFancy = 1;
    If_ManPerformMappingRound( p, p->pPars->nCutsMax, 0, 0 );
    p->pPars->fFancy = 0;

    // perform iterations over the circuit
    while ( !If_ManMappingSeqConverged( p ) )
    {
        // assign cuts to latches
        If_ManForEachLatch( p, pLatch, i )
            If_ObjPerformMappingLI( p, pLatch );
        // assign cuts to primary inputs
        If_ManForEachLatch( p, pLatch, i )
            If_ObjPerformMappingLO( p, pLatch, If_ManPi(p, If_ManPiNum(p) - If_ManPoNum(p) + i) );
        // map the nodes
        If_ManForEachNode( p, pObj, i )
            If_ObjPerformMapping( p, pObj, 0 );
    }

    if ( p->pPars->fVerbose )
    {
        PRT( "Total time", clock() - clkTotal );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutLift( If_Cut_t * pCut )
{
    unsigned i;
    for ( i = 0; i < pCut->nLeaves; i++ )
        pCut->pLeaves[i] = ((pCut->pLeaves[i] >> 8) << 8) | ((pCut->pLeaves[i] & 255) + 1);
}

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingLI( If_Man_t * p, If_Obj_t * pLatch )
{
    If_Obj_t * pFanin;
    int c;
    assert( If_ObjIsPo(pLatch) );
    pFanin = If_ObjFanin0(pLatch);
    for ( c = 0; c < pFanin->nCuts; c++ )
        If_CutCopy( pLatch->Cuts + c, pFanin->Cuts + c );
}

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingLO( If_Man_t * p, If_Obj_t * pLatch, If_Obj_t * pObj )
{
    If_Cut_t * pCut;
    int c, Limit = IF_MIN( p->nCuts + 1, p->nCutsUsed );
    assert( If_ObjIsPo(pLatch) );
    for ( c = 1; c < Limit; c++ )
    {
        pCut = pObj->Cuts + c;
        If_CutCopy( pCut, pLatch->Cuts + c - 1 );
        If_CutLift( pCut );
        pCut->Delay -= p->Fi;
    }
}

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManMappingSeqConverged( If_Man_t * p )
{
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


