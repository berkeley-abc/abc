/**CFile****************************************************************

  FileName    [utilFile.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Temporary file utilities.]

  Synopsis    [Temporary file utilities.]

  Author      [Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 29, 2010.]

  Revision    [$Id: utilFile.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/stat.h>

#if defined(_MSC_VER)
#include <Windows.h>
#include <process.h>
#include <io.h>
#else
#include <unistd.h>
#endif

#include "abc_global.h"

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
static ABC_UINT64_T realTimeAbs()  // -- absolute time in nano-seconds
{
#if defined(_MSC_VER)
    LARGE_INTEGER f, t;
    double realTime_freq;
    int ok;

    ok = QueryPerformanceFrequency(&f); assert(ok);
    realTime_freq = 1.0 / (__int64)(((ABC_UINT64_T)f.LowPart) | ((ABC_UINT64_T)f.HighPart << 32));

    ok = QueryPerformanceCounter(&t); assert(ok);
    return (ABC_UINT64_T)(__int64)(((__int64)(((ABC_UINT64_T)t.LowPart | ((ABC_UINT64_T)t.HighPart << 32))) * realTime_freq * 1000000000));
#endif
}

/**Function*************************************************************

  Synopsis    [Opens a temporary file.]

  Description [Opens a temporary file with given prefix and returns file 
  descriptor (-1 on failure) and a string containing the name of the file 
  (to be freed by caller).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int tmpFile(const char* prefix, const char* suffix, char** out_name)
{
#if defined(_MSC_VER)
    int i, fd;
    *out_name = (char*)malloc(strlen(prefix) + strlen(suffix) + 27);
    for (i = 0; i < 10; i++){
        sprintf(*out_name, "%s%I64X%d%s", prefix, realTimeAbs(), _getpid(), suffix);
        fd = _open(*out_name, O_CREAT | O_EXCL | O_BINARY | O_RDWR, _S_IREAD | _S_IWRITE);
        if (fd == -1){
            free(*out_name);
            *out_name = NULL;
        }
        return fd;
    }
    assert(0);  // -- could not open temporary file
    return 0;
#else
    int fd;
    *out_name = (char*)malloc(strlen(prefix) + strlen(suffix) + 7);
    assert(*out_name != NULL);
    sprintf(*out_name, "%sXXXXXX", prefix);
    fd = mkstemp(*out_name);
    if (fd == -1){
        free(*out_name);
        *out_name = NULL;
    }else{
        // Kludge:
        close(fd);
        unlink(*out_name);
        strcat(*out_name, suffix);
        fd = open(*out_name, O_CREAT | O_EXCL | O_RDWR, S_IREAD | S_IWRITE);
        if (fd == -1){
            free(*out_name);
            *out_name = NULL;
        }
    }
    return fd;
#endif
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
int main(int argc, char** argv)
{
    char* tmp_filename;
    int   fd = tmpFile("__abctmp_", &tmp_filename);
    FILE* out = fdopen(fd, "wb");

    fprintf(out, "This file contains important information.\n");
    fclose(out);

    printf("Created: %s\n", tmp_filename);
    free(tmp_filename);

    return 0;
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

