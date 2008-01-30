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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  Fpga_MappingPostProcess( Fpga_Man_t * p );

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
    int clk, clkTotal = clock();

    // collect the nodes reachable from POs in the DFS order (including the choices)
    p->vAnds = Fpga_MappingDfs( p, 1 );
    Fpga_ManReportChoices( p ); // recomputes levels
    Fpga_MappingSetChoiceLevels( p );

    // compute the cuts of nodes in the DFS order
    clk = clock();
    Fpga_MappingCuts( p );
    p->timeCuts = clock() - clk;

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
//PRT( "Total mapping time", clock() - clkTotal );

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
    int fShowSwitching    = 1;
    int fRecoverAreaFlow  = 1;
    int fRecoverArea      = 1;
    float aAreaTotalCur, aAreaTotalCur2;
    int Iter, clk;

    // compute area, set references, and collect nodes used in the mapping
    Iter = 1;
    aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
if ( p->fVerbose )
{
printf( "Iteration %dD :  Area = %8.1f  ", Iter++, aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Fpga_MappingGetSwitching(p,p->vMapping) );
PRT( "Time", p->timeMatch );
}

    if ( fRecoverAreaFlow )
    {
clk = clock();
        // compute the required times and the fanouts
        Fpga_TimeComputeRequiredGlobal( p );
        // remap topologically
        Fpga_MappingMatches( p, 0 );
        // get the resulting area
//        aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
        aAreaTotalCur = Fpga_MappingAreaTrav( p );
        // note that here we do not update the reference counter
        // for some reason, this works better on benchmarks
if ( p->fVerbose )
{
printf( "Iteration %dF :  Area = %8.1f  ", Iter++, aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Fpga_MappingGetSwitching(p,p->vMapping) );
PRT( "Time", clock() - clk );
}
    }

    // update reference counters
    aAreaTotalCur2 = Fpga_MappingSetRefsAndArea( p );
    assert( aAreaTotalCur == aAreaTotalCur2 );

    if ( fRecoverArea )
    {
clk = clock();
        // compute the required times and the fanouts
        Fpga_TimeComputeRequiredGlobal( p );
        // remap topologically
        if ( p->fSwitching )
            Fpga_MappingMatchesSwitch( p );
        else
            Fpga_MappingMatchesArea( p );
        // get the resulting area
        aAreaTotalCur = Fpga_MappingSetRefsAndArea( p );
if ( p->fVerbose )
{
printf( "Iteration %d%s :  Area = %8.1f  ", Iter++, (p->fSwitching?"S":"A"), aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Fpga_MappingGetSwitching(p,p->vMapping) );
PRT( "Time", clock() - clk );
}
    }

    p->fAreaGlo = aAreaTotalCur;
    return 1;
}


