/**CFile****************************************************************

  FileName    [io_test.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Output-routing regression tests.]

  Synopsis    [Shared declarations and checks active in release builds.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#ifndef ABC__test__io__io_test_h
#define ABC__test__io__io_test_h

#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START

extern void IoTestFail( const char * pExpr, const char * pFile, int Line );
extern void IoTestEmitC( const char * pTag );
extern void IoTestEmitCpp( const char * pTag );
extern void IoTestEmitBinary( void );
extern void IoTestEmitFile( FILE * pFile );

ABC_NAMESPACE_HEADER_END

// Do not put checks or side effects inside assert: CI uses NDEBUG.
#define IO_CHECK(expr) do { \
    if ( !(expr) ) \
        ABC_NAMESPACE_PREFIX IoTestFail(#expr, __FILE__, __LINE__); \
} while (0)

#endif
