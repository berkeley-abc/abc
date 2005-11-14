/**CFile****************************************************************

  FileName    [seqMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates sequential AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Seq_t * Seq_Create( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p;
    // start the manager
    p = ALLOC( Abc_Seq_t, 1 );
    memset( p, 0, sizeof(Abc_Seq_t) );
    p->pNtk  = pNtk;
    p->nSize = 1000;
    // create internal data structures
    p->vInits   = Vec_PtrStart( 2 * p->nSize ); 
    p->pMmInits = Extra_MmFixedStart( sizeof(Seq_Lat_t) );
    p->vLValues = Vec_IntStart( p->nSize ); 
    p->vLags    = Vec_StrStart( p->nSize ); 
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates sequential AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_Resize( Abc_Seq_t * p, int nMaxId )
{
    if ( p->nSize > nMaxId )
        return;
    p->nSize = nMaxId + 1;
    Vec_PtrFill( p->vInits,   2 * p->nSize, NULL ); 
    Vec_IntFill( p->vLValues, p->nSize, 0 ); 
    Vec_StrFill( p->vLags,    p->nSize, 0 ); 
}


/**Function*************************************************************

  Synopsis    [Deallocates sequential AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_Delete( Abc_Seq_t * p )
{
    if ( p->vMapAnds )  Vec_PtrFree( p->vMapAnds );  // the nodes used in the mapping
    if ( p->vMapCuts )  Vec_VecFree( p->vMapCuts );  // the cuts used in the mapping
    if ( p->vMapBags )  Vec_VecFree( p->vMapBags );  // the nodes included in the cuts used in the mapping
    if ( p->vMapLags )  Vec_VecFree( p->vMapLags );  // the lags of the mapped nodes

    if ( p->vBestCuts ) Vec_PtrFree( p->vBestCuts ); // the best cuts for nodes
    if ( p->vLValues )  Vec_IntFree( p->vLValues );  // the arrival times (L-Values of nodes)
    if ( p->vLags )     Vec_StrFree( p->vLags );     // the lags of the mapped nodes
    Vec_PtrFree( p->vInits );
    Extra_MmFixedStop( p->pMmInits, 0 );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


