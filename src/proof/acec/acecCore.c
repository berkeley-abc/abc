/**CFile****************************************************************

  FileName    [acecCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"

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
int Gia_PolynCec( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Cec_ParCec_t * pPars )
{
    Vec_Int_t * vOrder0 = Gia_PolynReorder( pGia0, pPars->fVerbose, pPars->fVeryVerbose );
    Vec_Int_t * vOrder1 = Gia_PolynReorder( pGia1, pPars->fVerbose, pPars->fVeryVerbose );
    Gia_PolynBuild( pGia0, vOrder0, 0, pPars->fVerbose, pPars->fVeryVerbose );
    Gia_PolynBuild( pGia1, vOrder1, 0, pPars->fVerbose, pPars->fVeryVerbose );
    Vec_IntFree( vOrder0 );
    Vec_IntFree( vOrder1 );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

