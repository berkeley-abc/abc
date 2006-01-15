/**CFile****************************************************************

  FileName    [aigUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManIncrementTravId( Aig_Man_t * pMan )
{
    Aig_Node_t * pObj;
    int i;
    if ( pMan->nTravIds == (1<<24)-1 )
    {
        pMan->nTravIds = 0;
        Aig_ManForEachNode( pMan, pObj, i )
            pObj->TravId = 0;
    }
    pMan->nTravIds++;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


