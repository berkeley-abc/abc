/**CFile****************************************************************

  FileName    [abc_stdio.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [Private build-time interception of C and C++ output.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#ifndef ABC__misc__util__abc_stdio_h
#define ABC__misc__util__abc_stdio_h

#define ABC_STDIO_REDIRECT 1

// Force-include only when compiling ABC. Never include from public headers.
// Read the C++ declarations before defining macros, including their #undefs.
#ifdef _WIN32
// The Microsoft CRT also declares perror in stdlib.h.
#include <stdlib.h>
#endif
#ifdef __cplusplus
#include <cstdio>
#include <functional>
#include <iostream>
// libc++ file streams call std::fwrite and std::fflush in inline definitions.
#include <fstream>
#ifdef _WIN32
// Parse string formatting before vecStr.h installs its legacy vsnprintf alias.
#include <string>
#endif
#endif
#include "abc_io.h"

#ifdef __cplusplus
ABC_NAMESPACE_CXX_HEADER_START
extern std::ostream & Abc_IoStream( int Stream );
ABC_NAMESPACE_CXX_HEADER_END

// std::cout becomes std::ref(...).get(); bare cout finds ref by ADL.
// No declarations are added to std, and the host's stream buffers are untouched.
#define cout ref( ::ABC_NAMESPACE_PREFIX Abc_IoStream(0) ).get()
#define cerr ref( ::ABC_NAMESPACE_PREFIX Abc_IoStream(1) ).get()
#endif

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
#define printf(...)       ABC_NAMESPACE_PREFIX Abc_IoFprintf(stdout, __VA_ARGS__)
#define fprintf(...)      ABC_NAMESPACE_PREFIX Abc_IoFprintf(__VA_ARGS__)
#define vprintf(...)      ABC_NAMESPACE_PREFIX Abc_IoVfprintf(stdout, __VA_ARGS__)
#define vfprintf(...)     ABC_NAMESPACE_PREFIX Abc_IoVfprintf(__VA_ARGS__)
#define puts(s)           ABC_NAMESPACE_PREFIX Abc_IoFprintf(stdout, "%s\n", (s))
#define fputs(...)        ABC_NAMESPACE_PREFIX Abc_IoFputs(__VA_ARGS__)
#define putchar(c)        ABC_NAMESPACE_PREFIX Abc_IoFputc((c), stdout)
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
