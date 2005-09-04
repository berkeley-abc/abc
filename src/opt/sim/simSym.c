/**CFile****************************************************************

  FileName    [simSym.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simulation to determine two-variable symmetries.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simSym.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes two variable symmetries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sim_ComputeTwoVarSymms( Abc_Ntk_t * pNtk )
{
    Sym_Man_t * p;
    Vec_Ptr_t * vResult;
    int Result;
    int i, clk = clock();

//    srand( time(NULL) );
    srand( 0xABC );

    // start the simulation manager
    p = Sym_ManStart( pNtk );
    p->nPairsTotal = Sim_UtilCountAllPairs( p->vSuppFun, p->nSimWords, p->vPairsTotal );

    // detect symmetries using circuit structure
    Sim_SymmsStructCompute( pNtk, p->vMatrSymms );
    p->nPairsSymm = p->nPairsSymmStr = Sim_UtilCountPairs( p->vMatrSymms, p->vPairsSym );

printf( "Total = %6d.  Sym = %6d.  NonSym = %6d.  Remaining = %6d.\n", 
       p->nPairsTotal, p->nPairsSymm, p->nPairsNonSymm, p->nPairsTotal-p->nPairsSymm-p->nPairsNonSymm );

    // detect symmetries using simulation
    for ( i = 1; i <= 1000; i++ )
    {
        // generate random pattern
        Sim_UtilGetRandom( p->uPatRand, p->nSimWords );
        // simulate this pattern
        Sim_SymmsSimulate( p, p->uPatRand, p->vMatrNonSymms );
        if ( i % 100 != 0 )
            continue;
        // count the number of pairs
        p->nPairsSymm    = Sim_UtilCountPairs( p->vMatrSymms,    p->vPairsSym );
        p->nPairsNonSymm = Sim_UtilCountPairs( p->vMatrNonSymms, p->vPairsNonSym );

printf( "Total = %6d.  Sym = %6d.  NonSym = %6d.  Remaining = %6d.\n", 
       p->nPairsTotal, p->nPairsSymm, p->nPairsNonSymm, p->nPairsTotal-p->nPairsSymm-p->nPairsNonSymm );
    }

    Result = p->nPairsSymm;
    vResult = p->vMatrSymms;  
    //  p->vMatrSymms = NULL;
    Sym_ManStop( p );
    return Result;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


