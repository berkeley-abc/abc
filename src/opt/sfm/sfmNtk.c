/**CFile****************************************************************

  FileName    [sfmNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Logic network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmNtk.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

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
Sfm_Ntk_t * Sfm_NtkAlloc( int nPis, int nPos, int nNodes, int nEdges )
{
    Sfm_Ntk_t * p;
    int AddOn = 2;
    int nSize = (nPis + nPos + nNodes) * (sizeof(Sfm_Obj_t) / sizeof(int) + AddOn) + 2 * nEdges;
    p = ABC_CALLOC( Sfm_Ntk_t, 1 );
    p->pMem = ABC_CALLOC( int, nSize );
    return p;
}
void Sfm_NtkFree( Sfm_Ntk_t * p )
{
    ABC_FREE( p->pMem );
    ABC_FREE( p->vObjs.pArray );
    ABC_FREE( p->vPis.pArray );
    ABC_FREE( p->vPos.pArray );
    ABC_FREE( p->vMem.pArray );
    ABC_FREE( p->vLevels.pArray );
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vSatVars.pArray );
    ABC_FREE( p->vTruths.pArray );
    ABC_FREE( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

