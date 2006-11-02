/**CFile****************************************************************

  FileName    [esopMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [SOP manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: esopMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "esop.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the minimization manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Esop_Man_t * Esop_ManAlloc( int nVars )
{
    Esop_Man_t * pMan;
    // start the manager
    pMan = ALLOC( Esop_Man_t, 1 );
    memset( pMan, 0, sizeof(Esop_Man_t) );
    pMan->nVars    = nVars;
    pMan->nWords   = Esop_BitWordNum( nVars * 2 );
    pMan->pMemMan1 = Mem_FixedStart( sizeof(Esop_Cube_t) + sizeof(unsigned) * (1 - 1) );
    pMan->pMemMan2 = Mem_FixedStart( sizeof(Esop_Cube_t) + sizeof(unsigned) * (2 - 1) );
    pMan->pMemMan4 = Mem_FixedStart( sizeof(Esop_Cube_t) + sizeof(unsigned) * (4 - 1) );
    pMan->pMemMan8 = Mem_FixedStart( sizeof(Esop_Cube_t) + sizeof(unsigned) * (8 - 1) );
    // allocate storage for the temporary cover
    pMan->ppStore = ALLOC( Esop_Cube_t *, pMan->nVars + 1 );
    // create tautology cubes
    Esop_ManClean( pMan, nVars );
    pMan->pOne0  = Esop_CubeAlloc( pMan );
    pMan->pOne1  = Esop_CubeAlloc( pMan );
    pMan->pTemp  = Esop_CubeAlloc( pMan );
    pMan->pBubble = Esop_CubeAlloc( pMan );  pMan->pBubble->uData[0] = 0;
    // create trivial cubes
    Esop_ManClean( pMan, 1 );
    pMan->pTriv0 = Esop_CubeAllocVar( pMan, 0, 0 );
    pMan->pTriv1 = Esop_CubeAllocVar( pMan, 0, 0 );
    Esop_ManClean( pMan, nVars );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Cleans the minimization manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Esop_ManClean( Esop_Man_t * p, int nSupp )
{
    // set the size of the cube manager
    p->nVars  = nSupp;
    p->nWords = Esop_BitWordNum(2*nSupp);
    // clean the storage
    memset( p->ppStore, 0, sizeof(Esop_Cube_t *) * (nSupp + 1) );
    p->nCubes = 0;
}

/**Function*************************************************************

  Synopsis    [Stops the minimization manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Esop_ManFree( Esop_Man_t * p )
{
    Mem_FixedStop ( p->pMemMan1, 0 );
    Mem_FixedStop ( p->pMemMan2, 0 );
    Mem_FixedStop ( p->pMemMan4, 0 );
    Mem_FixedStop ( p->pMemMan8, 0 );
    free( p->ppStore );
    free( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


