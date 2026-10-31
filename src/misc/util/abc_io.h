/**CFile****************************************************************

  FileName    [abc_io.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [Optional thread-local routing of standard C output.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#ifndef ABC__misc__util__abc_io_h
#define ABC__misc__util__abc_io_h

#include <stdio.h>
#include <stdarg.h>
#include "abc_namespaces.h"
#ifdef ABC_USE_PTHREADS
#if defined(_WIN32) && !defined(__MINGW32__)
#include "../../../lib/pthread.h"
#else
#include <pthread.h>
#endif
#endif

ABC_NAMESPACE_HEADER_START

#if defined(__GNUC__) || defined(__clang__)
#define ABC_IO_FORMAT(f,a) __attribute__((format(printf,f,a)))
#else
#define ABC_IO_FORMAT(f,a)
#endif

extern FILE * Abc_IoReadOut( void );
extern FILE * Abc_IoReadErr( void );
extern int    Abc_IoIsEnabled( void );
extern FILE * Abc_IoTempFile( void );
extern void   Abc_IoSetWorkerStreams( FILE * pOut, FILE * pErr );
extern int    Abc_IoPrintf( const char * pFormat, ... ) ABC_IO_FORMAT(1,2);
extern int    Abc_IoFprintf( FILE * pFile, const char * pFormat, ... ) ABC_IO_FORMAT(2,3);
extern int    Abc_IoVprintf( const char * pFormat, va_list Args ) ABC_IO_FORMAT(1,0);
extern int    Abc_IoVfprintf( FILE * pFile, const char * pFormat, va_list Args ) ABC_IO_FORMAT(2,0);
extern int    Abc_IoPuts( const char * pText );
extern int    Abc_IoFputs( const char * pText, FILE * pFile );
extern int    Abc_IoPutchar( int c );
extern int    Abc_IoFputc( int c, FILE * pFile );
extern size_t Abc_IoFwrite( const void * pData, size_t Size, size_t Count, FILE * pFile );
extern int    Abc_IoFflush( FILE * pFile );
extern void   Abc_IoPerror( const char * pText );
#ifdef ABC_USE_PTHREADS
extern int    Abc_IoThreadCreate( pthread_t * pThread, const pthread_attr_t * pAttr,
                                void * (*pFunc)(void *), void * pArg );
#endif

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
