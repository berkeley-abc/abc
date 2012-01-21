/**CFile****************************************************************

  FileName    [superInt.h]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Pre-computation of supergates.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 8, 2003.]

  Revision    [$Id: superInt.h,v 1.4 2004/07/06 04:55:59 alanmi Exp $]

***********************************************************************/

#ifndef ABC__map__super__superInt_h
#define ABC__map__super__superInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "src/base/abc/abc.h"
#include "src/base/main/mainInt.h"
#include "src/misc/mvc/mvc.h"
#include "src/map/mio/mio.h"
#include "src/misc/st/stmm.h"
#include "super.h"

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== superAnd.c =============================================================*/
extern void       Super2_Precompute( int nInputs, int nLevels, int fVerbose );
/*=== superGate.c =============================================================*/
extern void       Super_Precompute( Mio_Library_t * pLibGen, int nInputs, int nLevels, float tDelayMax, float tAreaMax, int TimeLimit, int fSkipInv, int fWriteOldFormat, int fVerbose );



ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
