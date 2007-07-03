/**CFile****************************************************************

  FileName    [fraCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraCore.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fraiging of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Fra_Perform( Dar_Man_t * pManAig, Fra_Par_t * pPars )
{
    Fra_Man_t * p;
    Dar_Man_t * pManAigNew;
    int clk;
    if ( Dar_ManNodeNum(pManAig) == 0 )
        return Dar_ManDup(pManAig);
clk = clock();
    assert( Dar_ManLatchNum(pManAig) == 0 );
    p = Fra_ManStart( pManAig, pPars );
    Fra_Simulate( p );
    Fra_Sweep( p );
    pManAigNew = p->pManFraig;
p->timeTotal = clock() - clk;
    Fra_ManStop( p );
    return pManAigNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


