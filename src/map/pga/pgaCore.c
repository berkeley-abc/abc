/**CFile****************************************************************

  FileName    [pgaCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [External APIs of the FPGA manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pgaCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pgaInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Pga_MappingInitCis( Pga_Man_t * p );

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
Vec_Ptr_t * Pga_DoMapping( Pga_Man_t * p )
{
    int fShowSwitching = 0;
    float aAreaTotalCur;
    int Iter, clk, clkTotal = clock();
    
    // assign the arrival times of the PIs
    Pga_MappingInitCis( p );

    // map the AIG for delay
clk = clock();
    Pga_MappingMatches( p, 0 );
p->timeDelay = clock() - clk;

    // compute area, set references, and collect nodes used in the mapping
    Iter = 1;
    aAreaTotalCur = Pga_MappingSetRefsAndArea( p );
if ( p->pParams->fVerbose )
{
printf( "Iteration %dD :  Area = %8.1f  ", Iter++, aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Pga_MappingGetSwitching(p) );
PRT( "Time", p->timeDelay );
}

    if ( p->pParams->fAreaFlow )
    {
clk = clock();
        // compute the required times and the fanouts
        Pga_MappingComputeRequired( p );
        // remap topologically
        Pga_MappingMatches( p, 1 );
p->timeAreaFlow = clock() - clk;
        // get the resulting area
        aAreaTotalCur = Pga_MappingSetRefsAndArea( p );
        // note that here we do not update the reference counter
        // for some reason, this works better on benchmarks
if ( p->pParams->fVerbose )
{
printf( "Iteration %dF :  Area = %8.1f  ", Iter++, aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Pga_MappingGetSwitching(p) );
PRT( "Time", p->timeAreaFlow );
}
    }

    if ( p->pParams->fArea )
    {
clk = clock();
        // compute the required times and the fanouts
        Pga_MappingComputeRequired( p );
        // remap topologically
        if ( p->pParams->fSwitching )
            Pga_MappingMatches( p, 3 );
        else
            Pga_MappingMatches( p, 2 );
p->timeArea = clock() - clk;
        // get the resulting area
        aAreaTotalCur = Pga_MappingSetRefsAndArea( p );
if ( p->pParams->fVerbose )
{
printf( "Iteration %d%s :  Area = %8.1f  ", Iter++, (p->pParams->fSwitching?"S":"A"), aAreaTotalCur );
if ( fShowSwitching )
printf( "Switch = %8.1f  ", Pga_MappingGetSwitching(p) );
PRT( "Time", p->timeArea );
}
    }
    p->AreaGlobal = aAreaTotalCur;

    if ( p->pParams->fVerbose )
        Pga_MappingPrintOutputArrivals( p );

    // return the mapping
    return Pga_MappingResults( p );
}

/**Function*************************************************************

  Synopsis    [Initializes the CI node arrival times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_MappingInitCis( Pga_Man_t * p )
{
    Pga_Node_t * pNode;
    float * pCiArrs;
    int i;
    // get the CI arrival times
    pCiArrs = Abc_NtkGetCiArrivalFloats( p->pParams->pNtk );
    // assign the arrival times of the PIs
    Pga_ManForEachCi( p, pNode, i )
        pNode->Match.Delay = pCiArrs[i];
    free( pCiArrs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


