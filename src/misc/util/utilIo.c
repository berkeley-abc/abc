/**CFile****************************************************************

  FileName    [utilIo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [Optional thread-local routing of standard C output.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#include "base/main/main.h"
#include "abc_io.h"
#include <errno.h>
#ifdef _WIN32
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Native workers inherit only streams, never their parent's mutable frame.
static ABC_THREAD_LOCAL FILE * s_pWorkerOut = NULL;
static ABC_THREAD_LOCAL FILE * s_pWorkerErr = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reports whether this library supports isolated capture.]

***********************************************************************/
int Abc_IoIsEnabled( void )
{
#if defined(ABC_STDIO_REDIRECT) && ABC_HAS_THREAD_LOCAL
    return 1;
#else
    return 0;
#endif
}

/**Function*************************************************************

  Synopsis    [Opens a binary temporary file deleted when its stream closes.]

  Description [The Windows CRT tmpfile uses the drive root, which may not be
  writable. Use the user's temporary directory and non-inheritable handles.]

***********************************************************************/
FILE * Abc_IoTempFile( void )
{
#ifdef _WIN32
    wchar_t Dir[MAX_PATH + 1], Name[MAX_PATH + 1];
    DWORD Length = GetTempPathW( MAX_PATH + 1, Dir );
    FILE * pFile;
    int Fd, Error;
    if ( Length == 0 || Length > MAX_PATH || !GetTempFileNameW(Dir, L"abc", 0, Name) )
    {
        errno = EIO;
        return NULL;
    }
    Fd = _wopen( Name, _O_RDWR | _O_BINARY | _O_TEMPORARY | _O_NOINHERIT );
    if ( Fd < 0 )
    {
        Error = errno;
        _wunlink( Name );
        errno = Error;
        return NULL;
    }
    pFile = _fdopen( Fd, "w+b" );
    if ( pFile == NULL )
    {
        Error = errno;
        _close( Fd );
        errno = Error;
    }
    return pFile;
#else
    return tmpfile();
#endif
}

/**Function*************************************************************

  Synopsis    [Installs inherited destinations in a dedicated worker.]

***********************************************************************/
void Abc_IoSetWorkerStreams( FILE * pOut, FILE * pErr )
{
    s_pWorkerOut = pOut;
    s_pWorkerErr = pErr;
}

/**Function*************************************************************

  Synopsis    [Reads the destination without allocating a frame.]

***********************************************************************/
FILE * Abc_IoReadOut( void )
{
    Abc_Frame_t * p = Abc_FrameReadGlobalFrame();
    FILE * pOut = p ? Abc_FrameReadOut(p) : stdout;
    // Bridge packets use the process streams, including direct descriptor I/O.
    if ( p && Abc_FrameIsBridgeMode() )
        return stdout;
    return pOut != stdout ? pOut : s_pWorkerOut ? s_pWorkerOut : stdout;
}
FILE * Abc_IoReadErr( void )
{
    Abc_Frame_t * p = Abc_FrameReadGlobalFrame();
    FILE * pErr = p ? Abc_FrameReadErr(p) : stderr;
    if ( p && Abc_FrameIsBridgeMode() )
        return stderr;
    return pErr != stderr ? pErr : s_pWorkerErr ? s_pWorkerErr : stderr;
}

/**Function*************************************************************

  Synopsis    [Maps console streams once; ordinary files pass through.]

***********************************************************************/
static FILE * Abc_IoFile( FILE * pFile )
{
    return pFile == stdout ? Abc_IoReadOut() : pFile == stderr ? Abc_IoReadErr() : pFile;
}

/**Function*************************************************************

  Synopsis    [Routes formatted output, preserving libc return values.]

***********************************************************************/
int Abc_IoVprintf( const char * pFormat, va_list Args )
{
    return (vfprintf)( Abc_IoReadOut(), pFormat, Args );
}
int Abc_IoVfprintf( FILE * pFile, const char * pFormat, va_list Args )
{
    return (vfprintf)( Abc_IoFile(pFile), pFormat, Args );
}
int Abc_IoPrintf( const char * pFormat, ... )
{
    int Ret;
    va_list Args;
    va_start( Args, pFormat );
    Ret = Abc_IoVprintf( pFormat, Args );
    va_end( Args );
    return Ret;
}
int Abc_IoFprintf( FILE * pFile, const char * pFormat, ... )
{
    int Ret;
    va_list Args;
    va_start( Args, pFormat );
    Ret = Abc_IoVfprintf( pFile, pFormat, Args );
    va_end( Args );
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Routes character/block output and flushing.]

***********************************************************************/
int Abc_IoPuts( const char * pText )
{
    return (fprintf)( Abc_IoReadOut(), "%s\n", pText );
}
int Abc_IoFputs( const char * pText, FILE * pFile )
{
    return (fputs)( pText, Abc_IoFile(pFile) );
}
int Abc_IoPutchar( int c )
{
    return (fputc)( c, Abc_IoReadOut() );
}
int Abc_IoFputc( int c, FILE * pFile )
{
    return (fputc)( c, Abc_IoFile(pFile) );
}
size_t Abc_IoFwrite( const void * pData, size_t Size, size_t Count, FILE * pFile )
{
    return (fwrite)( pData, Size, Count, Abc_IoFile(pFile) );
}
int Abc_IoFflush( FILE * pFile )
{
    // NULL retains libc's flush-all behavior.
    return (fflush)( Abc_IoFile(pFile) );
}
void Abc_IoPerror( const char * pText )
{
    int Error = errno;
    (fprintf)( Abc_IoReadErr(), "%s%s%s\n", pText ? pText : "",
               pText && pText[0] ? ": " : "", strerror(Error) );
    errno = Error;
}

#ifdef ABC_USE_PTHREADS
typedef struct Abc_IoThread_t_ Abc_IoThread_t;
struct Abc_IoThread_t_
{
    void * (*pFunc)(void *);
    void * pArg;
    FILE * pOut;
    FILE * pErr;
};

/**Function*************************************************************

  Synopsis    [Installs borrowed streams for the lifetime of a worker.]

***********************************************************************/
static void * Abc_IoThreadRun( void * pArg )
{
    Abc_IoThread_t Data = *(Abc_IoThread_t *)pArg;
    free( pArg );
    Abc_IoSetWorkerStreams( Data.pOut, Data.pErr );
    return Data.pFunc( Data.pArg );
}
int Abc_IoThreadCreate( pthread_t * pThread, const pthread_attr_t * pAttr,
                        void * (*pFunc)(void *), void * pArg )
{
    Abc_IoThread_t * p = (Abc_IoThread_t *)malloc( sizeof(Abc_IoThread_t) );
    int Ret;
    if ( p == NULL )
        return EAGAIN;
    p->pFunc = pFunc;
    p->pArg  = pArg;
    p->pOut  = Abc_IoReadOut();
    p->pErr  = Abc_IoReadErr();
    Ret = (pthread_create)( pThread, pAttr, Abc_IoThreadRun, p );
    if ( Ret )
        free( p );
    return Ret;
}
#endif

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
