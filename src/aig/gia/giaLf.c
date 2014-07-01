/**CFile****************************************************************

  FileName    [giaLf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaLf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecSet.h"

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
void Lf_ManSetDefaultPars( Jf_Par_t * pPars )
{
    Jf_ManSetDefaultPars( pPars );
}
Gia_Man_t * Lf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    return Jf_ManPerformMapping( pGia, pPars );
}
Gia_Man_t * Gia_ManPerformLfMapping( Gia_Man_t * p, Jf_Par_t * pPars, int fNormalized )
{
    return Jf_ManPerformMapping( p, pPars );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

