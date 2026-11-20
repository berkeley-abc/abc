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

ABC_NAMESPACE_IMPL_START


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
void If_ManSetDefaultPars( If_Par_t * pPars )
{
    memset( pPars, 0, sizeof(If_Par_t) );
    pPars->nLutSize    = -1;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.005;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  1;
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fPower      =  0;
    pPars->fCutMin     =  0;
    pPars->fBidec      =  0;
    pPars->fUserLutDec =  0;
    pPars->fUserLut2D  =  0;
    pPars->fVerbose    =  0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If_ManPerformMappingCombTimed( If_Man_t * p, abctime Deadline );

/**Function*************************************************************

  Synopsis    [Sets up cut storage and runs the combinational mapper with a deadline.]

***********************************************************************/
int If_ManPerformMappingTimed( If_Man_t * p, abctime Deadline )
{
    p->pPars->fAreaOnly = p->pPars->fArea; // temporary
    // create the CI cutsets
    If_ManSetupCiCutSets( p );
    // allocate memory for other cutsets
    If_ManSetupSetAll( p, If_ManCrossCut(p) );
    // derive reverse top order
    p->vObjsRev = If_ManReverseOrder( p );
    return If_ManPerformMappingCombTimed( p, Deadline );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMapping( If_Man_t * p )
{
    return If_ManPerformMappingTimed( p, 0 );
}

int If_ManPerformMappingComb( If_Man_t * p )
{
    return If_ManPerformMappingCombTimed( p, 0 );
}

/**Function*************************************************************

  Synopsis    [Runs the mapping rounds within the supplied deadline.]

***********************************************************************/
static int If_ManPerformMappingCombTimed( If_Man_t * p, abctime Deadline )
{
    If_Obj_t * pObj;
    abctime clkTotal = Abc_Clock();
    int i;

    //p->vVisited2 = Vec_IntAlloc( 100 );
    //p->vMarks = Vec_StrStart( If_ManObjNum(p) );

    // set arrival times and fanout estimates
    If_ManForEachCi( p, pObj, i )
    {
        If_ObjSetArrTime( pObj, p->pPars->pTimesArr ? p->pPars->pTimesArr[i] : (float)0.0 );
        pObj->EstRefs = (float)1.0;
    }

    // delay oriented mapping
    if ( p->pPars->fPreprocess && !p->pPars->fArea )
    {
        // map for delay
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 0, 1, 1, "Delay", Deadline ) ) return 0;

        // map for delay second option
        p->pPars->fFancy = 1;
        If_ManResetOriginalRefs( p );
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 0, 1, 0, "Delay-2", Deadline ) )
        { p->pPars->fFancy = 0; return 0; }
        p->pPars->fFancy = 0;
        // map for area
        p->pPars->fArea = 1;
        If_ManResetOriginalRefs( p );
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 0, 1, 0, "Area", Deadline ) )
        { p->pPars->fArea = 0; return 0; }
        p->pPars->fArea = 0;
    }
    else
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 0, 0, 1, "Delay", Deadline ) ) return 0;

    // try to improve area by expanding and reducing the cuts
    if ( p->pPars->fExpRed )
        If_ManImproveMapping( p );

    // area flow oriented mapping
    for ( i = 0; i < p->pPars->nFlowIters; i++ )
    {
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 1, 0, 0, "Flow", Deadline ) ) return 0;
        if ( p->pPars->fExpRed )
            If_ManImproveMapping( p );
    }

    // area oriented mapping
    for ( i = 0; i < p->pPars->nAreaIters; i++ )
    {
        if ( p->pPars->fDumpFile && p->pPars->nLutSize <= 6 && i == p->pPars->nAreaIters-1 ) {
            p->vCuts = Vec_IntAlloc( 1 << 20 );
            p->vCutCosts = Vec_IntAlloc( 1 << 16 );
        }
        if ( !If_ManPerformMappingRoundTimed( p, p->pPars->nCutsMax, 2, 0, 0, "Area", Deadline ) ) return 0;
        if ( p->pPars->fExpRed )
            If_ManImproveMapping( p );
    }

    if ( p->pPars->fVerbose )
    {
//        Abc_Print( 1, "Total memory = %7.2f MB. Peak cut memory = %7.2f MB.  ", 
//            1.0 * (p->nObjBytes + 2*sizeof(void *)) * If_ManObjNum(p) / (1<<20), 
//            1.0 * p->nSetBytes * Mem_FixedReadMaxEntriesUsed(p->pMemSet) / (1<<20) );
        Abc_PrintTime( 1, "Total time", Abc_Clock() - clkTotal );
    }
//    Abc_Print( 1, "Cross cut memory = %d.\n", Mem_FixedReadMaxEntriesUsed(p->pMemSet) );
//    Abc_Print( 1, "Special POs = %d.\n", If_ManCountSpecialPos(p) );

/*
    {
        static ABC_THREAD_LOCAL char * pLastName = NULL;
        FILE * pTable = fopen( "fpga/ucsb/stats.txt", "a+" );
        if ( pLastName == NULL || strcmp(pLastName, p->pName) )
        {
            fprintf( pTable, "\n" );
            fprintf( pTable, "%s ", p->pName );

            fprintf( pTable, "%d ", If_ManCiNum(p) );
            fprintf( pTable, "%d ", If_ManCoNum(p) );
            fprintf( pTable, "%d ", If_ManAndNum(p) );

            ABC_FREE( pLastName );
            pLastName = Abc_UtilStrsav( p->pName );
        }

        fprintf( pTable, "%d ", (int)p->AreaGlo );
        fprintf( pTable, "%d ", (int)p->RequiredGlo );
        fclose( pTable );
    }
*/
    p->pPars->FinalDelay = p->RequiredGlo;
    p->pPars->FinalArea  = p->AreaGlo;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
