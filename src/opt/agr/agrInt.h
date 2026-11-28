/**CFile****************************************************************

  FileName    [agrInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Internal declarations.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrInt.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#ifndef ABC__opt__agr__agrInt_h
#define ABC__opt__agr__agrInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "opt/pa/paInt.h"
#include "base/main/main.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

// prints only during "agr -v"
#define AGR_VERBOSE( ... )                  \
    do                                      \
    {                                       \
        if ( Agr_IsVerbose() )              \
            Abc_Print( 1, __VA_ARGS__ );    \
    } while ( 0 )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== agrBlock.cpp ======================================================*/
extern int           Agr_RunBlock( Abc_Frame_t * pAbc, int nRoots );
extern void          Agr_ResetBlock( void );
extern void          Agr_SetVerbose( int fVerbose );
extern int           Agr_IsVerbose( void );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
