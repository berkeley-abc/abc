/**CFile****************************************************************

  FileName    [io_test.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Output-routing regression tests.]

  Synopsis    [Exercises the public API as an external library consumer.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - October 31, 2026.]

***********************************************************************/

#include "io_test.h"
#include "base/main/main.h"
#include "misc/util/abc_io.h"
#include <atomic>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#ifdef _WIN32
#include <windows.h>
#include <io.h>
#else
#include <fcntl.h>
#include <unistd.h>
#endif

#if defined(printf) || defined(fprintf) || defined(pthread_create) || defined(ABC_STDIO_REDIRECT)
#error ABC output interception must not leak into the host application
#endif

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Fails visibly even in release builds and captured contexts.]

***********************************************************************/
void IoTestFail( const char * pExpr, const char * pFile, int Line )
{
    std::fprintf( stderr, "%s:%d: check failed: %s\n", pFile, Line, pExpr );
    std::abort();
}

/**Function*************************************************************

  Synopsis    [Remembers a native handle while its FILE is still valid.]

***********************************************************************/
#ifdef _WIN32
typedef HANDLE IoTestHandle_t;
#else
typedef int IoTestHandle_t;
#endif
static IoTestHandle_t IoTestHandle( FILE * pFile )
{
#ifdef _WIN32
    intptr_t Handle = _get_osfhandle( _fileno(pFile) );
    IO_CHECK( Handle != -1 && Handle != -2 );
    return (HANDLE)Handle;
#else
    int Fd = fileno( pFile );
    IO_CHECK( Fd >= 0 );
    return Fd;
#endif
}

/**Function*************************************************************

  Synopsis    [Checks lifetime without passing a closed descriptor to the CRT.]

***********************************************************************/
static void IoTestHandleCheck( IoTestHandle_t Handle, bool fOpen )
{
#ifdef _WIN32
    DWORD Flags;
    BOOL Result = GetHandleInformation( Handle, &Flags );
    IO_CHECK( fOpen ? Result != 0 : Result == 0 && GetLastError() == ERROR_INVALID_HANDLE );
#else
    errno = 0;
    int Result = fcntl( Handle, F_GETFD );
    IO_CHECK( fOpen ? Result >= 0 : Result == -1 && errno == EBADF );
#endif
}

/**Function*************************************************************

  Synopsis    [Creates a unique named file for the set-command tests.]

***********************************************************************/
static std::string IoTestPath( void )
{
#ifdef _WIN32
    char Dir[MAX_PATH + 1], Path[MAX_PATH + 1];
    DWORD Length = GetTempPathA( MAX_PATH + 1, Dir );
    IO_CHECK( Length > 0 && Length <= MAX_PATH );
    IO_CHECK( GetTempFileNameA(Dir, "abc", 0, Path) != 0 );
    // ABC command strings accept forward slashes on Windows, without escapes.
    for ( char * p = Path; *p; ++p )
        if ( *p == '\\' )
            *p = '/';
#else
    char Path[] = "/tmp/abc-io-test-XXXXXX";
    int Fd = mkstemp( Path );
    IO_CHECK( Fd >= 0 && close(Fd) == 0 );
#endif
    return Path;
}

/**Function*************************************************************

  Synopsis    [Checks a failed Windows log allocation leaves no current frame.]

***********************************************************************/
static void IoTestTempFailure( void )
{
#ifdef _WIN32
    wchar_t Dir[MAX_PATH + 1], Path[MAX_PATH + 1];
    DWORD Length = GetTempPathW( MAX_PATH + 1, Dir );
    IO_CHECK( Length > 0 && Length <= MAX_PATH );
    IO_CHECK( GetTempFileNameW(Dir, L"abc", 0, Path) != 0 );
    DWORD OldLength = GetEnvironmentVariableW( L"TMP", NULL, 0 );
    std::wstring Old( OldLength ? OldLength : 1, L'\0' );
    if ( OldLength )
        IO_CHECK( GetEnvironmentVariableW(L"TMP", &Old[0], OldLength) == OldLength - 1 );
    // A file cannot be used as a directory; no elevated privileges are needed.
    IO_CHECK( SetEnvironmentVariableW(L"TMP", Path) );
    errno = 0;
    Abc_Frame_t * pFrame = Abc_FrameCreateWithLog();
    int Error = errno;
    IO_CHECK( SetEnvironmentVariableW(L"TMP", OldLength ? Old.c_str() : NULL) );
    IO_CHECK( DeleteFileW(Path) );
    IO_CHECK( pFrame == NULL && Error != 0 );
    IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
#endif
}

/**Function*************************************************************

  Synopsis    [Reads a temporary file without discarding embedded zero bytes.]

***********************************************************************/
static std::string IoTestRead( FILE * pFile )
{
    char Buffer[4096];
    size_t nBytes;
    std::string Result;
    IO_CHECK( std::fflush(pFile) == 0 );
    IO_CHECK( std::fseek(pFile, 0, SEEK_SET) == 0 );
    while ( (nBytes = std::fread(Buffer, 1, sizeof(Buffer), pFile)) != 0 )
        Result.append( Buffer, nBytes );
    IO_CHECK( !std::ferror(pFile) );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Uses the public copy API after commands and workers finish.]

***********************************************************************/
static std::string IoTestLog( Abc_Frame_t * pFrame )
{
    FILE * pFile = Abc_IoTempFile();
    IO_CHECK( pFile != NULL );
    IO_CHECK( Abc_FrameCopyLog(pFrame, pFile) );
    std::string Result = IoTestRead( pFile );
    IO_CHECK( std::fclose(pFile) == 0 );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Counts tagged messages without depending on their ordering.]

***********************************************************************/
static int IoTestCount( const std::string & Text, const std::string & Tag )
{
    int Count = 0;
    size_t Pos = 0;
    while ( (Pos = Text.find(Tag, Pos)) != std::string::npos )
    {
        ++Count;
        Pos += Tag.size();
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Executes a command with a scoped current frame.]

***********************************************************************/
static int IoTestCommand( Abc_Frame_t * pFrame, const std::string & Command )
{
    Abc_Frame_t * pPrevious = Abc_FrameEnter( pFrame );
    int Status = Cmd_CommandExecute( pFrame, Command.c_str() );
    Abc_FrameLeave( pPrevious );
    return Status;
}

/**Function*************************************************************

  Synopsis    [Checks ordinary console output with interception on or off.]

***********************************************************************/
static void IoTestConsole( void )
{
    Abc_Frame_t * pFrame = Abc_FrameCreate();
    IO_CHECK( pFrame != NULL && !Abc_FrameHasLog(pFrame) );
    Abc_Frame_t * pPrevious = Abc_FrameEnter( pFrame );
    IO_CHECK( pPrevious == NULL );
    IoTestEmitC( "console" );
    IoTestEmitCpp( "console" );
    Abc_FrameLeave( pPrevious );
    Abc_FrameDestroy( pFrame );
    IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
}

/**Function*************************************************************

  Synopsis    [Checks borrowed and command-owned stream lifetimes in both modes.]

***********************************************************************/
static void IoTestStreams( void )
{
    std::string Path = IoTestPath();
    FILE * pBorrowed = Abc_IoTempFile();
    IO_CHECK( pBorrowed != NULL );
    IoTestHandle_t Borrowed = IoTestHandle( pBorrowed );
    Abc_Frame_t * pFrame = Abc_FrameCreate();
    IO_CHECK( pFrame != NULL );
    std::string Redirect = std::string("set abcout \"") + Path + '"';
    IO_CHECK( IoTestCommand(pFrame, Redirect) == 0 );
    IoTestHandle_t Owned = IoTestHandle( Abc_FrameReadOut(pFrame) );
    IO_CHECK( Abc_FrameSetOutputStreams(pFrame, pBorrowed, pBorrowed) );
    IoTestHandleCheck( Owned, false );
    IO_CHECK( IoTestCommand(pFrame, "echo BORROWED") == 0 );
    Abc_FrameDestroy( pFrame );
    IoTestHandleCheck( Borrowed, true );
    IO_CHECK( IoTestRead(pBorrowed) == "BORROWED \n" );
    IO_CHECK( std::fclose(pBorrowed) == 0 );

    pFrame = Abc_FrameCreate();
    IO_CHECK( pFrame != NULL );
    IO_CHECK( IoTestCommand(pFrame, Redirect) == 0 );
    Owned = IoTestHandle( Abc_FrameReadOut(pFrame) );
    Abc_FrameDestroy( pFrame );
    IoTestHandleCheck( Owned, false );
    IO_CHECK( std::remove(Path.c_str()) == 0 );
    IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
}

/**Function*************************************************************

  Synopsis    [Checks independent frames and both kinds of worker thread.]

***********************************************************************/
static void IoTestParallel( Abc_Frame_t * pFrames[2], const std::string & Load )
{
    const char * pTags[2] = { "ALPHA_PRIVATE", "BETA_PRIVATE" };
    std::atomic<int> Ready( 0 );
    std::thread Workers[2];
    for ( int i = 0; i < 2; ++i )
        IO_CHECK( IoTestCommand(pFrames[i], Load) == 0 );
    for ( int i = 0; i < 2; ++i )
        Workers[i] = std::thread( [&, i]() {
            Abc_Frame_t * pPrevious = Abc_FrameEnter( pFrames[i] );
            IO_CHECK( pPrevious == NULL );
            ++Ready;
            while ( Ready.load() != 2 )
                std::this_thread::yield();
            for ( int k = 0; k < 4; ++k )
            {
                IoTestEmitC( pTags[i] );
                IoTestEmitCpp( pTags[i] );
                IoTestEmitBinary();
            }
            IO_CHECK( Cmd_CommandExecute(pFrames[i], "&rrr -J 2 -N 2 -V 2 -O 1") == 0 );
            std::string BadCommand = std::string("unknown_command_") + pTags[i];
            IO_CHECK( Cmd_CommandExecute(pFrames[i], BadCommand.c_str()) != 0 );
            Abc_FrameLeave( pPrevious );
            IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
        } );
    for ( int i = 0; i < 2; ++i )
        Workers[i].join();
    for ( int i = 0; i < 2; ++i )
    {
        std::string Log = IoTestLog( pFrames[i] );
        IO_CHECK( Log.find(pTags[1-i]) == std::string::npos );
        IO_CHECK( IoTestCount(Log, std::string("C:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("C-ERR:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("C-WORKER:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("C-WORKER-ERR:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("CPP:") + pTags[i] + ":002a\n") == 4 );
        IO_CHECK( IoTestCount(Log, std::string("CPP-ERR:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("CPP-WORKER:") + pTags[i] + '\n') == 4 );
        IO_CHECK( IoTestCount(Log, std::string("BIN:A\0B\r\n\032Z\n", 12)) == 4 );
        IO_CHECK( IoTestCount(Log, "DEC:42\n") == 4 );
        IO_CHECK( Log.find("stats summary") != std::string::npos );
        IO_CHECK( Log.find(std::string("unknown_command_") + pTags[i]) != std::string::npos );
    }
}

/**Function*************************************************************

  Synopsis    [Checks nested scopes, explicit files, copy/append and ownership.]

***********************************************************************/
static void IoTestScopes( Abc_Frame_t * pFrames[2] )
{
    std::string Path = IoTestPath();
    FILE * pFile = Abc_IoTempFile();
    IO_CHECK( pFile != NULL );
    Abc_Frame_t * pPrevious = Abc_FrameEnter( pFrames[0] );
    IO_CHECK( pPrevious == NULL );
    Abc_Frame_t * pOuter = Abc_FrameEnter( pFrames[1] );
    IO_CHECK( pOuter == pFrames[0] );
    IoTestEmitC( "nested_beta" );
    Abc_FrameLeave( pOuter );
    IoTestEmitCpp( "restored_alpha" );
    IoTestEmitFile( pFile );
    IoTestEmitCppFile( Path.c_str() );
    // Host calls must still reach the real console while ABC capture is active.
    std::printf( "HOST stdout\n" );
    std::fprintf( stderr, "HOST stderr\n" );
    errno = 0;
    IO_CHECK( !Abc_FrameSetOutputStreams(pFrames[0], pFile, pFile) && errno == EBUSY );
    IO_CHECK( Cmd_CommandExecute(pFrames[0], "set abcout -") != 0 );
    IO_CHECK( Cmd_CommandExecute(pFrames[0], "set abcerr -") != 0 );
    Abc_FrameSetBridgeMode();
    IO_CHECK( !Abc_FrameIsBridgeMode() );
    errno = 0;
    IO_CHECK( !Abc_FrameCopyLog(pFrames[0], Abc_FrameReadOut(pFrames[0])) && errno == EINVAL );
    Abc_FrameLeave( pPrevious );

    std::string Alpha = IoTestLog( pFrames[0] ), Beta = IoTestLog( pFrames[1] );
    IO_CHECK( IoTestCount(Alpha, "Cannot enable bridge mode for a captured frame.\n") == 1 );
    IO_CHECK( Beta.find("Cannot enable bridge mode") == std::string::npos );
    IO_CHECK( Alpha.find("restored_alpha") != std::string::npos );
    IO_CHECK( Alpha.find("nested_beta") == std::string::npos );
    IO_CHECK( Beta.find("nested_beta") != std::string::npos );
    IO_CHECK( Beta.find("restored_alpha") == std::string::npos );
    IO_CHECK( Alpha.find("HOST ") == std::string::npos && Beta.find("HOST ") == std::string::npos );
    IO_CHECK( Alpha.find("ordinary file") == std::string::npos );
    IO_CHECK( Alpha.find("ordinary C++ file") == std::string::npos );
    IO_CHECK( IoTestRead(pFile) == "ordinary file\ndata" );
    IO_CHECK( std::fclose(pFile) == 0 );
    pFile = std::fopen( Path.c_str(), "rb" );
    IO_CHECK( pFile != NULL );
    IO_CHECK( IoTestRead(pFile) == "ordinary C++ file\n" );
    IO_CHECK( std::fclose(pFile) == 0 );
    IO_CHECK( std::remove(Path.c_str()) == 0 );
    IO_CHECK( IoTestCommand(pFrames[0], "echo AFTER_COPY") == 0 );
    IO_CHECK( IoTestLog(pFrames[0]) == Alpha + "AFTER_COPY \n" );
}

/**Function*************************************************************

  Synopsis    [Checks that destruction closes a private log, even if ignored.]

***********************************************************************/
static void IoTestDestroy( Abc_Frame_t * pFrame )
{
    IoTestHandle_t Handle = IoTestHandle( Abc_FrameReadOut(pFrame) );
#ifdef _WIN32
    DWORD Flags;
    IO_CHECK( GetHandleInformation(Handle, &Flags) && !(Flags & HANDLE_FLAG_INHERIT) );
#endif
    Abc_FrameDestroy( pFrame );
    IoTestHandleCheck( Handle, false );
    IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
}

ABC_NAMESPACE_IMPL_END

ABC_NAMESPACE_USING_NAMESPACE

/**Function*************************************************************

  Synopsis    [Runs under CTest, which also checks the host's stdout/stderr.]

***********************************************************************/
int main( int argc, char ** argv )
{
    IO_CHECK( argc == 3 );
    IO_CHECK( std::strcmp(argv[2], "ON") == 0 || std::strcmp(argv[2], "OFF") == 0 );
    IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
    IoTestConsole();
    IoTestStreams();
    if ( std::strcmp(argv[2], "OFF") == 0 )
    {
        IO_CHECK( !Abc_IoIsEnabled() );
        errno = 0;
        IO_CHECK( Abc_FrameCreateWithLog() == NULL && errno == ENOSYS );
        IO_CHECK( Abc_FrameReadGlobalFrame() == NULL );
        std::puts( "PASS disabled" );
        return 0;
    }
    IO_CHECK( Abc_IoIsEnabled() );
    IoTestTempFailure();
    Abc_Frame_t * pFrames[2] = { Abc_FrameCreateWithLog(), Abc_FrameCreateWithLog() };
    IO_CHECK( pFrames[0] != NULL && pFrames[1] != NULL );
    IO_CHECK( Abc_FrameHasLog(pFrames[0]) && Abc_FrameHasLog(pFrames[1]) );
    IO_CHECK( Abc_FrameReadOut(pFrames[0]) != Abc_FrameReadOut(pFrames[1]) );
    for ( int i = 0; i < 2; ++i )
        IO_CHECK( Abc_FrameReadOut(pFrames[i]) == Abc_FrameReadErr(pFrames[i]) );
    std::string Load = std::string("read_blif \"") + argv[1] + "\"; strash; &get";
    IoTestParallel( pFrames, Load );
    // Exercise the real std::thread and native pthread launch sites as well.
    IO_CHECK( IoTestCommand(pFrames[0], Load + "; &eslim -W 2 30 -I 2 -R 1 -S 5 -V 2 -Z 1 -i") == 0 );
    IO_CHECK( IoTestCommand(pFrames[1], Load + "; &eslim2 -P 2 -W 2 30 -D 1 -I 2 -R 1 -S 5 -V 2 -Z 1 -i") == 0 );
    IO_CHECK( IoTestLog(pFrames[0]).find("Total #iterations:") != std::string::npos );
    IO_CHECK( IoTestLog(pFrames[1]).find("Total #iterations:") != std::string::npos );
    IoTestScopes( pFrames );
    IoTestDestroy( pFrames[0] );
    IoTestDestroy( pFrames[1] );
    for ( int i = 0; i < 3; ++i )
    {
        Abc_Frame_t * pFrame = Abc_FrameCreateWithLog();
        IO_CHECK( pFrame != NULL );
        IoTestDestroy( pFrame );
    }
    std::puts( "PASS capture" );
    return 0;
}
