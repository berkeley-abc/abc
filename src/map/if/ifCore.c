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

static int If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode );

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
    int nItersFlow = 2;
    int nItersArea = 1;
    int clkTotal = clock();
    int i;
    // set arrival times and trivial cuts at const 1 and PIs
    If_ManConst1(p)->Cuts[0].Delay = 0.0;
    If_ManForEachPi( p, pObj, i )
        pObj->Cuts[0].Delay = p->pPars->pTimesArr[i];
    // set the fanout estimates of the PIs
    If_ManForEachPi( p, pObj, i )
        pObj->EstRefs = (float)1.0;
    // delay oriented mapping
    If_ManPerformMappingRound( p, p->pPars->nCutsMax, 0 );
    // area flow oriented mapping
    for ( i = 0; i < nItersFlow; i++ )
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 1 );
    // area oriented mapping
    for ( i = 0; i < nItersArea; i++ )
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 2 );
    if ( p->pPars->fVerbose )
    {
        PRT( "Total time", clock() - clkTotal );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode )
{
    If_Obj_t * pObj;
    int i, clk = clock();
    assert( Mode >= 0 && Mode <= 2 );
    // set the cut number
    p->nCutsUsed   = nCutsUsed;
    p->nCutsMerged = 0;
    p->nCutsMax    = 0;
    // map the internal nodes
    If_ManForEachNode( p, pObj, i )
        If_ObjPerformMapping( p, pObj, Mode );
    // compute required times and stats
    If_ManComputeRequired( p, Mode==0 );
    if ( p->pPars->fVerbose )
    {
        char Symb = (Mode == 0)? 'D' : ((Mode == 1)? 'F' : 'A');
        printf( "%c:  Del = %6.2f. Area = %8.2f. Cuts = %6d. Lim = %2d. Ave = %5.2f. ", 
            Symb, p->RequiredGlo, p->AreaGlo, p->nCutsMerged, p->nCutsUsed, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
        PRT( "T", clock() - clk );
//    printf( "Max number of cuts = %d. Average number of cuts = %5.2f.\n", 
//        p->nCutsMax, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


