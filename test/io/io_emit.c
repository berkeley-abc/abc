/**CFile****************************************************************

  FileName    [io_emit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Output-routing regression tests.]

  Synopsis    [C stdio and inherited native-worker output.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#include "io_test.h"
#include "misc/util/abc_io.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Emits identifiable output from an intercepted pthread.]

***********************************************************************/
static void * IoTestWorker( void * pArg )
{
    const char * pTag = (const char *)pArg;
    IO_CHECK( printf("C-WORKER:%s\n", pTag) > 0 );
    IO_CHECK( fprintf(stderr, "C-WORKER-ERR:%s\n", pTag) > 0 );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Emits C output and joins a worker before returning.]

***********************************************************************/
void IoTestEmitC( const char * pTag )
{
    pthread_t Thread;
    IO_CHECK( printf("C:%s\n", pTag) > 0 );
    IO_CHECK( fprintf(stderr, "C-ERR:%s\n", pTag) > 0 );
    IO_CHECK( pthread_create(&Thread, NULL, IoTestWorker, (void *)pTag) == 0 );
    IO_CHECK( pthread_join(Thread, NULL) == 0 );
}

/**Function*************************************************************

  Synopsis    [Checks that an ordinary file remains an explicit destination.]

***********************************************************************/
void IoTestEmitFile( FILE * pFile )
{
    IO_CHECK( fprintf(pFile, "ordinary file\n") == 14 );
    IO_CHECK( fwrite("data", 1, 4, pFile) == 4 );
    IO_CHECK( fflush(pFile) == 0 );
}

ABC_NAMESPACE_IMPL_END
