/**CFile****************************************************************

  FileName    [fpgaCore.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [Technology mapping for variable-size-LUT FPGAs.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 2.0. Started - August 18, 2004.]

  Revision    [$Id: fpgaCore.c,v 1.7 2004/10/01 23:41:04 satrajit Exp $]

***********************************************************************/

#include "fpgaInt.h"
//#include "res.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int   Fpga_MappingPostProcess( Fpga_Man_t * p );

extern void  Fpga_Experiment( Fpga_Man_t * p );
extern void Fpga_MappingCutsSeq( Fpga_Man_t * p );
extern void Fpga_MappingLValues( Fpga_Man_t * pMan, int fVerbose );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs technology mapping for the given object graph.]

  Description [The object graph is stored in the mapping manager.
  First, all the AND-nodes, which fanout into the POs, are collected
  in the DFS fashion. Next, three steps are performed: the k-feasible
  cuts are computed for each node, the truth tables are computed for
  each cut, and the delay-optimal matches are assigned for each node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fpga_Mapping( Fpga_Man_t * p )
{
    int clk;

    // collect the nodes reachable from POs in the DFS order (including the choices)
    p->vAnds = Fpga_MappingDfs( p, 1 );
    Fpga_ManReportChoices( p ); // recomputes levels
    Fpga_MappingSetChoiceLevels( p );

    if ( p->fSequential )
    {
//        Fpga_MappingCutsSeq( p );
        Fpga_MappingCuts( p );
//clk = clock();
//        Fpga_MappingLValues( p, p->fVerbose );
//PRT( "Time", clock() - clk );
        return 0;
    }

    // compute the cuts of nodes in the DFS order
    clk = clock();
    Fpga_MappingCuts( p );
    p->timeCuts = clock() - clk;

//    Fpga_MappingSortByLevel( p, p->vAnds, 1 );

    // derive the truth tables 
    clk = clock();
//    Fpga_MappingTruths( p );
    p->timeTruth = clock() - clk;

    // match the truth tables to the supergates
    clk = clock();
    if ( !Fpga_MappingMatches( p, 1 ) )
        return 0;
    p->timeMatch = clock() - clk;

    // perform area recovery
    if ( p->fAreaRecovery )
    {
        clk = clock();
        if ( !Fpga_MappingPostProcess( p ) )
            return 0;
        p->timeRecover = clock() - clk;
    }

    // perform resynthesis
//    if ( p->fResynthesis )
//        Res_Resynthesize( p, p->DelayLimit, p->AreaLimit, p->TimeLimit, 1 );

    // print the AI-graph used for mapping
    //Fpga_ManShow( p, "test" );
    if ( p->fVerbose )
        Fpga_MappingPrintOutputArrivals( p );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Postprocesses the mapped network for area recovery.]

  Description [This procedure assumes that the mapping is assigned.
  It iterates the loop, in which the required times are computed and
  the mapping is updated. It is conceptually similar to the paper: 
  V. Manohararajah, S. D. Brown, Z. G. Vranesic, Heuristics for area 
  minimization in LUT-based FGPA technology mapping. Proc. IWLS '04.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fpga_MappingPostProcess( Fpga_Man_t * p )
{
    float aAreaTotalPrev, aAreaTotalCur, aAreaTotalCur2;
    float aSwitchTotalPrev, aSwitchTotalCur;
    int Iter, clk;


if ( p->fVerbose )
{
printf( "Iteration %dD :  Area = %11.1f  ", 0, Fpga_MappingArea( p ) );
PRT( "Time", p->timeMatch );
}


//    Fpga_MappingExplore( p );
//    p->fAreaGlo = Fpga_MappingArea( p );
//    return;


//    aAreaTotalCur = FPGA_FLOAT_LARGE;
    aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );

    Iter = 1;
    do {
clk = clock();
        // save the previous area flow
        aAreaTotalPrev = aAreaTotalCur;

        // compute the required times and the fanouts
        Fpga_TimeComputeRequiredGlobal( p );
        // remap topologically
        Fpga_MappingMatches( p, 0 );
        // get the resulting area
        aAreaTotalCur = Fpga_MappingArea( p );
if ( p->fVerbose )
{
printf( "Iteration %dF :  Area = %11.1f  ", Iter++, aAreaTotalCur );
PRT( "Time", clock() - clk );
}
        if ( p->fPower )
            aSwitchTotalCur = Fpga_MappingPrintSwitching( p );
        // quit if this iteration reduced area flow by less than 1%
    } while ( aAreaTotalPrev > 1.02 * aAreaTotalCur );


//    Fpga_MappingExplore( p );
//    p->fAreaGlo = Fpga_MappingArea( p );
//    return;


/*
    // compute the area of each cut
    aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
    // compute the required times and the fanouts
    Fpga_TimeComputeRequiredGlobal( p );
    // perform experiment
    Fpga_Experiment( p );
*/


    // compute the area of each cut
    aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
    aAreaTotalCur2 = Fpga_MappingComputeCutAreas( p );
    assert( aAreaTotalCur == aAreaTotalCur2 );


//    aAreaTotalCur = FPGA_FLOAT_LARGE;
//    Iter = 1;
    do {
clk = clock();
        // save the previous area flow
        aAreaTotalPrev = aAreaTotalCur;

        // compute the required times and the fanouts
        Fpga_TimeComputeRequiredGlobal( p );
        // remap topologically
        Fpga_MappingMatchesArea( p );
        // get the resulting area
        aAreaTotalCur = Fpga_MappingArea( p );
if ( p->fVerbose )
{
printf( "Iteration %dA :  Area = %11.1f  ", Iter++, aAreaTotalCur );
PRT( "Time", clock() - clk );
}
        if ( p->fPower )
        {
            aSwitchTotalPrev = aSwitchTotalCur;
            aSwitchTotalCur  = Fpga_MappingPrintSwitching( p );
        }
        // quit if this iteration reduced area flow by less than 1%
    } while ( aAreaTotalPrev > 1.02 * aAreaTotalCur );


    if ( p->fPower )
    {
        do {
clk = clock();
            // save the previous area flow
            aAreaTotalPrev = aAreaTotalCur;

            // compute the required times and the fanouts
            Fpga_TimeComputeRequiredGlobal( p );
            // remap topologically
            Fpga_MappingMatchesSwitch( p );
            // get the resulting area
            aAreaTotalCur = Fpga_MappingArea( p );
if ( p->fVerbose )
{
printf( "Iteration %dS :  Area = %11.1f  ", Iter++, aAreaTotalCur );
PRT( "Time", clock() - clk );
}
            aSwitchTotalPrev = aSwitchTotalCur;
            aSwitchTotalCur  = Fpga_MappingPrintSwitching( p );
            // quit if this iteration reduced area flow by less than 1%
        } while ( aSwitchTotalPrev > 1.01 * aSwitchTotalCur );
    }

/*
    // compute the area of each cut
    aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
    // compute the required times and the fanouts
    Fpga_TimeComputeRequiredGlobal( p );
    // perform experiment
    Fpga_Experiment( p );
*/
    p->fAreaGlo = aAreaTotalCur;
    return 1;
}


