/**CFile****************************************************************

  FileName    [abc_print.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [C stdio emission of locally formatted C++ diagnostics.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#ifndef ABC__misc__util__abc_print_h
#define ABC__misc__util__abc_print_h

#include <cstdio>
#include <sstream>
#include "abc_namespaces.h"

ABC_NAMESPACE_CXX_HEADER_START

/**Function*************************************************************

  Synopsis    [Emits a formatted message, including embedded zero bytes.]

***********************************************************************/
static inline void Abc_PrintString( FILE * pFile, const std::string & Text, bool fFlush = false )
{
    fwrite( Text.data(), 1, Text.size(), pFile );
    if ( fFlush )
        fflush( pFile );
}

ABC_NAMESPACE_CXX_HEADER_END

// Preserve type-specific formatting for containers, bitsets and manipulators.
// Formatting state is local; complete messages enter the same C stdio path.
#define ABC_PRINT_STREAM(file, flush, ...) do { \
    std::ostringstream abcPrintBuffer; \
    abcPrintBuffer << __VA_ARGS__; \
    ABC_NAMESPACE_PREFIX Abc_PrintString(file, abcPrintBuffer.str(), flush); \
} while (0)

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
