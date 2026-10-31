/**CFile****************************************************************

  FileName    [abc_stdio.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [Private build-time interception of C output calls.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#ifndef ABC__misc__util__abc_stdio_h
#define ABC__misc__util__abc_stdio_h

#define ABC_STDIO_REDIRECT 1

// Force-include only when compiling ABC. Never include from public headers.
// Read the C++ declarations before defining macros, including their #undefs.
#ifdef __cplusplus
#include <cstdio>
#ifdef _WIN32
// Parse string formatting before vecStr.h installs its legacy vsnprintf alias.
#include <string>
#endif
#endif
#include "abc_io.h"

#undef printf
#undef fprintf
#undef vprintf
#undef vfprintf
#undef puts
#undef fputs
#undef putchar
#undef fputc
#undef putc
#undef fwrite
#undef fflush
#undef perror
#define printf(...)       ABC_NAMESPACE_PREFIX Abc_IoPrintf(__VA_ARGS__)
#define fprintf(...)      ABC_NAMESPACE_PREFIX Abc_IoFprintf(__VA_ARGS__)
#define vprintf(...)      ABC_NAMESPACE_PREFIX Abc_IoVprintf(__VA_ARGS__)
#define vfprintf(...)     ABC_NAMESPACE_PREFIX Abc_IoVfprintf(__VA_ARGS__)
#define puts(...)         ABC_NAMESPACE_PREFIX Abc_IoPuts(__VA_ARGS__)
#define fputs(...)        ABC_NAMESPACE_PREFIX Abc_IoFputs(__VA_ARGS__)
#define putchar(...)      ABC_NAMESPACE_PREFIX Abc_IoPutchar(__VA_ARGS__)
#define fputc(...)        ABC_NAMESPACE_PREFIX Abc_IoFputc(__VA_ARGS__)
#define putc(...)         ABC_NAMESPACE_PREFIX Abc_IoFputc(__VA_ARGS__)
#define fwrite(...)       ABC_NAMESPACE_PREFIX Abc_IoFwrite(__VA_ARGS__)
#define fflush(...)       ABC_NAMESPACE_PREFIX Abc_IoFflush(__VA_ARGS__)
#define perror(...)       ABC_NAMESPACE_PREFIX Abc_IoPerror(__VA_ARGS__)
#ifdef ABC_USE_PTHREADS
#define pthread_create(...) ABC_NAMESPACE_PREFIX Abc_IoThreadCreate(__VA_ARGS__)
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
