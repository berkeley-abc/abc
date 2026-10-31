/**CFile****************************************************************

  FileName    [io_emit.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Output-routing regression tests.]

  Synopsis    [C++ formatting and explicit worker-stream inheritance.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#include "io_test.h"
#include "misc/util/abc_io.h"
#include "misc/util/abc_print.h"
#include <iomanip>
#include <thread>

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Uses the same formatting and worker APIs as ABC packages.]

***********************************************************************/
void IoTestEmitCpp( const char * pTag )
{
    FILE * pOut = Abc_IoReadOut(), * pErr = Abc_IoReadErr();
    ABC_PRINT_STREAM( stdout, true,
        "CPP:" << pTag << ':' << std::setfill('0') << std::setw(4) << std::hex << 42 << '\n' );
    IO_CHECK( fprintf(stderr, "CPP-ERR:%s\n", pTag) > 0 );
    std::thread Worker( [pTag, pOut, pErr]() {
        Abc_IoSetWorkerStreams( pOut, pErr );
        ABC_PRINT_STREAM( stdout, true, "CPP-WORKER:" << pTag << '\n' );
    } );
    Worker.join();
}

/**Function*************************************************************

  Synopsis    [Checks binary-safe emission and local formatting state.]

***********************************************************************/
void IoTestEmitBinary( void )
{
    Abc_PrintString( stdout, std::string("BIN:A\0B\r\n\032Z\n", 12), true );
    ABC_PRINT_STREAM( stdout, true, "DEC:" << 42 << '\n' );
}

ABC_NAMESPACE_IMPL_END
