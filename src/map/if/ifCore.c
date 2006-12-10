/**CFile****************************************************************

  FileName    [ifCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [The central part of the mapper.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifCore.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

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
int If_ManPerformMapping( If_Man_t * p )
{
    If_Obj_t * pObj;
    int nItersFlow = 1;
    int nItersArea = 2;
    int clkTotal = clock();
    int RetValue, i;

    // try sequential mapping
    if ( p->pPars->fSeqMap )
    {
        RetValue = If_ManPerformMappingSeq( p );
        if ( p->pPars->fVerbose )
        {
            PRT( "Total time", clock() - clkTotal );
        }
        return RetValue;
    }

    // set arrival times and trivial cuts at const 1 and PIs
    If_ManConst1(p)->Cuts[0].Delay = 0.0;
    If_ManForEachCi( p, pObj, i )
        pObj->Cuts[0].Delay = p->pPars->pTimesArr[i];
    // set the fanout estimates of the PIs
    If_ManForEachCi( p, pObj, i )
        pObj->EstRefs = (float)1.0;
    // delay oriented mapping
    if ( p->pPars->fPreprocess && !p->pPars->fArea && p->pPars->nCutsMax >= 4  )
        If_ManPerformMappingPreprocess( p );
    else
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 0, 1, "Delay" );
    // try to improve area by expanding and reducing the cuts
    if ( p->pPars->fExpRed && !p->pPars->fTruth )
        If_ManImproveMapping( p );
    // area flow oriented mapping
    for ( i = 0; i < nItersFlow; i++ )
    {
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 1, 1, "Flow" );
        if ( p->pPars->fExpRed && !p->pPars->fTruth )
            If_ManImproveMapping( p );
    }
    // area oriented mapping
    for ( i = 0; i < nItersArea; i++ )
    {
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 2, 1, "Area" );
        if ( p->pPars->fExpRed && !p->pPars->fTruth )
            If_ManImproveMapping( p );
    }
    if ( p->pPars->fVerbose )
    {
        PRT( "Total time", clock() - clkTotal );
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


