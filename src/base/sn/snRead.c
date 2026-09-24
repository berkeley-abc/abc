/**CFile****************************************************************

  FileName    [snRead.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [External companion invocation and transactional HDL import.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snRead.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
// Expose POSIX declarations (notably readlink) in strict C99 builds. Feature-test
// macros must precede every system header; respect an explicitly selected level.
#if !defined(_WIN32) && !defined(WIN32) && !defined(_MSC_VER) && !defined(__MINGW32__) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif


#include "snRead.h"
#include <string.h>

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <windows.h>
#else
#include <unistd.h>
#if defined(__APPLE__)
#include <mach-o/dyld.h>
#endif
#endif

ABC_NAMESPACE_IMPL_START
int Sn_IsHdlFile( const char * pFileName )
{
    const char * pExtension = pFileName ? strrchr(pFileName, '.') : NULL;
    return pExtension && (!strcmp(pExtension, ".v") || !strcmp(pExtension, ".sv"));
}

sn_design_t * Sn_ReadVerifyHdl( int nFiles, char ** ppFiles, const char * pTop,
                               Vec_Ptr_t * vDefines, sn_module_id_t * pTopId, FILE * pError )
{
    Sn_ReadOptions_t Options = {0};
    Options.pTop = pTop;
    Options.vDefines = vDefines;
    Options.fPreserveState = 1;
    Options.fStrictModules = 1;
    return Sn_ReadHdl(nFiles, ppFiles, &Options, pTopId, pError);
}

int Sn_TempPrefix( char * pBuffer, size_t nBuffer, const char * pStem )
{
    int Written;
#if defined(_MSC_VER) || defined(__MINGW32__)
    Written = snprintf( pBuffer, nBuffer, "%s\\%s", Abc_GetTmpDir(), pStem );
#else
    Written = snprintf( pBuffer, nBuffer, "%s/%s", Abc_GetTmpDir(), pStem );
#endif
    return Written >= 0 && (size_t)Written < nBuffer;
}




int Sn_MapLutExecutable( char * pBuffer, size_t nBuffer )
{
    if ( pBuffer == NULL || nBuffer < 2 || nBuffer > UINT32_MAX )
        return 0;
#if defined(_MSC_VER) || defined(__MINGW32__)
    DWORD Length = GetModuleFileNameA( NULL, pBuffer, (DWORD)nBuffer );
    return Length > 0 && Length < nBuffer;
#elif defined(__APPLE__)
    uint32_t Size = (uint32_t)nBuffer;
    return _NSGetExecutablePath( pBuffer, &Size ) == 0;
#else
    // readlink does not terminate its result. Give it the full capacity so an
    // exact-capacity result is detected as truncation, not accepted as a path.
    ssize_t Length = readlink( "/proc/self/exe", pBuffer, nBuffer );
    if ( Length <= 0 || (size_t)Length >= nBuffer )
        return 0;
    pBuffer[Length] = '\0';
    return 1;
#endif
}

ABC_NAMESPACE_IMPL_END


// Windows builds retain SN-file processing and GIA extraction, but never invoke the Slang companion.
#if defined(_WIN32) || defined(WIN32) || defined(_MSC_VER) || defined(__MINGW32__)
ABC_NAMESPACE_IMPL_START
sn_design_t * Sn_ReadHdl( int nFiles, char ** ppFiles, const Sn_ReadOptions_t * pOptions,
                         sn_module_id_t * pTop, FILE * pError )
{
    (void)nFiles;
    (void)ppFiles;
    (void)pOptions;
    if ( pTop ) *pTop = SN_INVALID_ID;
    fprintf(pError ? pError : stderr,
        "HDL loading through Slang is not supported in this Windows build.\n"
        "Use '@read design.sn' with an SN file produced on Linux or macOS,\n"
        "or provide AIGER files to '&cec'.\n");
    return NULL;
}
ABC_NAMESPACE_IMPL_END
#else

#include "snCheck.h"
#include <errno.h>
#include "base/main/main.h"
#include <sys/types.h>
#if !defined(__wasm)
#include <sys/wait.h>
#endif


ABC_NAMESPACE_IMPL_START
extern int tmpFile( const char * pPrefix, const char * pSuffix, char ** ppFileName );

static char * Sn_SlangExecutable( void )
{
    static char Companion[4096];
    char * pSlash;
    char * pExecutable = Abc_FrameReadFlag( (char *)"sn" );
    if ( pExecutable != NULL )
        return pExecutable;
    if ( Sn_MapLutExecutable(Companion, sizeof(Companion)) )
    {
        pSlash = strrchr( Companion, '/' );
        if ( pSlash && (size_t)(pSlash + 1 - Companion) + sizeof("sn.exe") <= sizeof(Companion) )
        {
            strcpy( pSlash + 1, "sn" );
            if ( access(Companion, X_OK) == 0 )
                return Companion;
        }
    }
    return (char *)"sn";
}

static int Sn_RunProcess( char ** ppArgs )
{
#if defined(__wasm)
    (void)ppArgs;
    return -1;
#else
    pid_t Child = fork();
    int Status;
    if ( Child < 0 )
        return -1;
    if ( Child == 0 )
    {
        execvp( ppArgs[0], ppArgs );
        // execvp() returns only on failure. Release the child copy so memory checkers do not report it as leaked;
        // the parent's copy is unaffected and is freed by the caller.
        ABC_FREE( ppArgs );
        _exit( 127 );
    }
    pid_t Waited;
    do { Waited = waitpid(Child, &Status, 0); } while (Waited < 0 && errno == EINTR);
    if ( Waited != Child )
        return -1;
    return WIFEXITED(Status) ? WEXITSTATUS(Status) : -1;
#endif
}





sn_design_t * Sn_ReadHdl( int nFiles, char ** ppFiles, const Sn_ReadOptions_t * pOptions,
                         sn_module_id_t * pTop, FILE * pError )
{
    Sn_ReadOptions_t Defaults = {0};
    sn_design_t * pDesign = NULL;
    char Prefix[512], * pTemp = NULL, * pDefine;
    Vec_Ptr_t * vArgs;
    FILE * pFile;
    int File, Status, i, End, Failed;
    if ( !pError ) pError = stderr;
    if ( !pOptions ) pOptions = &Defaults;
    if ( !pTop || nFiles < 1 || !ppFiles ) return NULL;
    *pTop = SN_INVALID_ID;
    for ( i = 0; i < nFiles; ++i )
    {
        pFile = fopen(ppFiles[i], "r");
        if ( !pFile ) { fprintf(pError, "Cannot open HDL input '%s'.\n", ppFiles[i]); return NULL; }
        fclose(pFile);
    }
    if ( !Sn_TempPrefix(Prefix, sizeof(Prefix), "sn_") )
    { fprintf(pError, "Temporary SN path is too long.\n"); return NULL; }
    File = tmpFile(Prefix, ".sn", &pTemp);
    if ( File < 0 ) { fprintf(pError, "Cannot create temporary SN file.\n"); return NULL; }
    close(File);
    vArgs = Vec_PtrAlloc(16);
    Vec_PtrPush(vArgs, Sn_SlangExecutable());
    if ( pOptions->pTop ) { Vec_PtrPush(vArgs, (void *)"-M"); Vec_PtrPush(vArgs, (void *)pOptions->pTop); }
    if ( pOptions->vDefines )
        Vec_PtrForEachEntry(char *, pOptions->vDefines, pDefine, i)
        { Vec_PtrPush(vArgs, (void *)"-D"); Vec_PtrPush(vArgs, pDefine); }
    if ( pOptions->vBlackboxes )
        Vec_PtrForEachEntry(char *, pOptions->vBlackboxes, pDefine, i)
        { Vec_PtrPush(vArgs, (void *)"-B"); Vec_PtrPush(vArgs, pDefine); }
    if ( pOptions->fPreserveState ) Vec_PtrPush(vArgs, (void *)"-p");
    if ( pOptions->fStrictModules ) Vec_PtrPush(vArgs, (void *)"-s");
    if ( pOptions->fVerbose ) Vec_PtrPush(vArgs, (void *)"-t");
    Vec_PtrPush(vArgs, (void *)"-o");
    Vec_PtrPush(vArgs, pTemp);
    for ( i = 0; i < nFiles; ++i ) Vec_PtrPush(vArgs, ppFiles[i]);
    Vec_PtrPush(vArgs, NULL);
    if ( pOptions->fVerbose )
    {
        fprintf(pError, "External SN command:");
        for ( i = 0; i + 1 < Vec_PtrSize(vArgs); ++i )
            fprintf(pError, " '%s'", (char *)Vec_PtrEntry(vArgs, i));
        fprintf(pError, "\n");
    }
    Status = Sn_RunProcess((char **)Vec_PtrArray(vArgs));
    Vec_PtrFree(vArgs);
    if ( Status )
    {
        fprintf(pError, "External SN frontend failed with status %d.\n", Status);
        if ( Status == -1 || Status == 127 )
            fprintf(pError, "Check 'set sn /path/to/sn', the companion beside ABC, or PATH.\n");
        goto cleanup;
    }
    pFile = fopen(pTemp, "rb");
    if ( !pFile ) { fprintf(pError, "Cannot open companion output '%s'.\n", pTemp); goto cleanup; }
    pDesign = sn_design_read_binary_checked(pFile, pError);
    End = fgetc(pFile);
    Failed = ferror(pFile);
    Failed |= fclose(pFile) != 0;
    if ( pDesign && (End != EOF || Failed || !pDesign->modules.size || !sn_design_is_topo(pDesign)) )
    {
        fprintf(pError, "Invalid companion output: %s.\n", Failed ? "SN file read/close error" :
            End != EOF ? "trailing data" : !pDesign->modules.size ? "empty design" : "modules not topologically ordered");
        sn_design_destroy(pDesign); pDesign = NULL;
    }
    if ( pDesign )
    {
        *pTop = pOptions->pTop ? sn_design_find_module(pDesign, pOptions->pTop) :
                                (sn_module_id_t)(pDesign->modules.size - 1);
        if ( *pTop == SN_INVALID_ID )
        {
            fprintf(pError, "Companion output has no top module '%s'.\n", pOptions->pTop);
            sn_design_destroy(pDesign); pDesign = NULL;
        }
    }
cleanup:
    remove(pTemp);
    ABC_FREE(pTemp);
    return pDesign;
}
ABC_NAMESPACE_IMPL_END
#endif
