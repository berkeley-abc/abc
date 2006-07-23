/**CFile****************************************************************

  FileName    [playerMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: playerMan.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the PLA/LUT mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pla_Man_t * Pla_ManAlloc( Ivy_Man_t * pAig, int nLutMax, int nPlaMax )
{
    Pla_Man_t * pMan;
    assert( !(nLutMax < 2 || nLutMax > 8 || nPlaMax < 8 || nPlaMax > 128)  );
    // start the manager
    pMan = ALLOC( Pla_Man_t, 1 );
    memset( pMan, 0, sizeof(Pla_Man_t) );
    pMan->nLutMax   = nLutMax;
    pMan->nPlaMax   = nPlaMax;
    pMan->nCubesMax = 2 * nPlaMax; // higher limit, later reduced
    pMan->pManAig   = pAig;
    // set up the temporaries
    pMan->vComTo0 = Vec_IntAlloc( 2 * nPlaMax );
    pMan->vComTo1 = Vec_IntAlloc( 2 * nPlaMax );
    pMan->vPairs0 = Vec_IntAlloc( nPlaMax );
    pMan->vPairs1 = Vec_IntAlloc( nPlaMax );
    pMan->vTriv0  = Vec_IntAlloc( 1 );  Vec_IntPush( pMan->vTriv0, -1 ); 
    pMan->vTriv1  = Vec_IntAlloc( 1 );  Vec_IntPush( pMan->vTriv1, -1 ); 
    // allocate memory for object structures
    pMan->pPlaStrs = ALLOC( Pla_Obj_t, sizeof(Pla_Obj_t) * (Ivy_ManObjIdMax(pAig)+1) );
    memset( pMan->pPlaStrs, 0, sizeof(Pla_Obj_t) * (Ivy_ManObjIdMax(pAig)+1) );
    // create the cube manager
    pMan->pManMin = Esop_ManAlloc( nPlaMax );
    // save the resulting manager
    assert( pAig->pData == NULL );
    pAig->pData = pMan;
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Frees the PLA/LUT mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFree( Pla_Man_t * p )
{
    Pla_Obj_t * pStr;
    int i;
    Esop_ManFree( p->pManMin );
    Vec_IntFree( p->vTriv0 );
    Vec_IntFree( p->vTriv1 );
    Vec_IntFree( p->vComTo0 );
    Vec_IntFree( p->vComTo1 );
    Vec_IntFree( p->vPairs0 );
    Vec_IntFree( p->vPairs1 );
    for ( i = 0, pStr = p->pPlaStrs; i <= Ivy_ManObjIdMax(p->pManAig); i++, pStr++ )
        FREE( pStr->vSupp[0].pArray ), FREE( pStr->vSupp[1].pArray );
    free( p->pPlaStrs );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Cleans the PLA/LUT structure of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFreeStr( Pla_Man_t * p, Pla_Obj_t * pStr )
{
    if ( pStr->pCover[0] != PLA_EMPTY )  Esop_CoverRecycle( p->pManMin, pStr->pCover[0] );
    if ( pStr->pCover[1] != PLA_EMPTY )  Esop_CoverRecycle( p->pManMin, pStr->pCover[1] );
    if ( pStr->vSupp[0].pArray )         free( pStr->vSupp[0].pArray );
    if ( pStr->vSupp[1].pArray )         free( pStr->vSupp[1].pArray );
    memset( pStr, 0, sizeof(Pla_Obj_t) );
    pStr->pCover[0] = PLA_EMPTY;
    pStr->pCover[1] = PLA_EMPTY;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


