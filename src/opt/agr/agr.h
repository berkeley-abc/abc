/**CFile****************************************************************

  FileName    [agr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [External declarations.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agr.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#ifndef ABC__opt__agr__agr_h
#define ABC__opt__agr__agr_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "base/main/main.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== agrCommand.cpp ====================================================*/
extern void          Agr_Init( Abc_Frame_t * pAbc );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
