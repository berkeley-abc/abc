/**CFile****************************************************************

  FileName    [mvcProc.c]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Various boolean procedures working with covers.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: mvcOpBool.c,v 1.4 2003/04/16 01:55:37 alanmi Exp $]

***********************************************************************/

#include "mvc.h"

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
Mvc_Cover_t * Mvc_CoverBooleanOr( Mvc_Cover_t * pCover1, Mvc_Cover_t * pCover2 )
{
    Mvc_Cover_t * pCover;
    Mvc_Cube_t * pCube, * pCubeCopy;
    // make sure the covers are compatible
    assert( pCover1->nBits == pCover2->nBits );
    // clone the cover
    pCover = Mvc_CoverClone( pCover1 );
    // create the cubes by making pair-wise products
    // of cubes in pCover1 and pCover2
    Mvc_CoverForEachCube( pCover1, pCube )
    {
        pCubeCopy = Mvc_CubeDup( pCover, pCube );
        Mvc_CoverAddCubeTail( pCover, pCubeCopy );
    }
    Mvc_CoverForEachCube( pCover2, pCube )
    {
        pCubeCopy = Mvc_CubeDup( pCover, pCube );
        Mvc_CoverAddCubeTail( pCover, pCubeCopy );
    }
    return pCover;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

