/**CFile****************************************************************

  FileName    [wlnRtl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Word-level network.]

  Synopsis    [Constructing WLN network from Rtl data structure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 23, 2018.]

  Revision    [$Id: wlnRtl.c,v 1.00 2018/09/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wln.h"
#include "aig/aig/aig.h"
#include "aig/gia/giaAig.h"
#include "base/io/ioAbc.h"
#include "base/main/main.h"

#ifdef WIN32
#include <process.h> 
#define unlink _unlink
#else
#include <unistd.h>
#endif

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
#define MAX_LINE 1000000

void Rtl_NtkCleanFile( char * pFileName )
{
    char * pBuffer, * pFileName2 = "_temp__.rtlil"; 
    FILE * pFile = fopen( pFileName, "rb" );
    FILE * pFile2;
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return;
    }
    pFile2 = fopen( pFileName2, "wb" );
    if ( pFile2 == NULL )
    {
        fclose( pFile );
        printf( "Cannot open file \"%s\" for writing.\n", pFileName2 );
        return;
    }
    pBuffer = ABC_ALLOC( char, MAX_LINE );
    while ( fgets( pBuffer, MAX_LINE, pFile ) != NULL )
        if ( !strstr(pBuffer, "attribute \\src") )
            fputs( pBuffer, pFile2 );
    ABC_FREE( pBuffer );
    fclose( pFile );
    fclose( pFile2 );
}

void Rtl_NtkCleanFile2( char * pFileName )
{
    char * pBuffer, * pFileName2 = "_temp__.v"; 
    FILE * pFile = fopen( pFileName, "rb" );
    FILE * pFile2;
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return;
    }
    pFile2 = fopen( pFileName2, "wb" );
    if ( pFile2 == NULL )
    {
        fclose( pFile );
        printf( "Cannot open file \"%s\" for writing.\n", pFileName2 );
        return;
    }
    pBuffer = ABC_ALLOC( char, MAX_LINE );
    while ( fgets( pBuffer, MAX_LINE, pFile ) != NULL )
        if ( !strstr(pBuffer, "//") )
            fputs( pBuffer, pFile2 );
    ABC_FREE( pBuffer );
    fclose( pFile );
    fclose( pFile2 );
}

char * Wln_GetYosysName()
{
    char * pYosysName = NULL;
    char * pYosysNameWin = "yosys.exe";
    char * pYosysNameUnix = "yosys";
    if ( Abc_FrameReadFlag("yosyswin") )
        pYosysNameWin = Abc_FrameReadFlag("yosyswin");
    if ( Abc_FrameReadFlag("yosysunix") )
        pYosysNameUnix = Abc_FrameReadFlag("yosysunix");
#ifdef WIN32
    pYosysName = pYosysNameWin;
#else
    pYosysName = pYosysNameUnix;
#endif
    return pYosysName;
}
static char * Wln_FileNamesJoin( char ** ppFileNames, int nFileNames )
{
    char * pFileNames;
    int i, nChars = 1;
    for ( i = 0; i < nFileNames; i++ )
        nChars += strlen( ppFileNames[i] ) + 1;
    pFileNames = ABC_ALLOC( char, nChars );
    pFileNames[0] = 0;
    for ( i = 0; i < nFileNames; i++ )
    {
        if ( i )
            strcat( pFileNames, " " );
        strcat( pFileNames, ppFileNames[i] );
    }
    return pFileNames;
}
static int Wln_FileNamesHasSv( char ** ppFileNames, int nFileNames )
{
    int i;
    for ( i = 0; i < nFileNames; i++ )
        if ( strstr( ppFileNames[i], ".sv" ) != NULL )
            return 1;
    return 0;
}
int Wln_ConvertToRtl( char * pCommand, char * pFileTemp )
{
#if defined(__wasm)
    return 0;
#else
    FILE * pFile;
    if ( system( pCommand ) == -1 )
    {
        fprintf( stdout, "Cannot execute \"%s\".\n", pCommand );
        return 0;
    }
    if ( (pFile = fopen(pFileTemp, "r")) == NULL )
    {
        fprintf( stdout, "Cannot open intermediate file \"%s\".\n", pFileTemp );
        return 0;
    }
    fclose( pFile );
    return 1;
#endif
}
Rtl_Lib_t * Wln_ReadSystemVerilog( char ** ppFileNames, int nFileNames, char * pTopModule, char * pDefines, int fCollapse, int fVerbose )
{
    Rtl_Lib_t * pNtk = NULL;
    char * pFileNames, * pCommand;
    char * pFileTemp = "_temp_.rtlil";
    int fSVlog = Wln_FileNamesHasSv(ppFileNames, nFileNames);
    int nCommand;
    if ( nFileNames == 1 && strstr(ppFileNames[0], ".rtl") )
        return Rtl_LibReadFile( ppFileNames[0], ppFileNames[0] );
    pFileNames = Wln_FileNamesJoin( ppFileNames, nFileNames );
    nCommand = strlen(Wln_GetYosysName()) + strlen(pFileNames) + (pDefines ? strlen(pDefines) : 0) + (pTopModule ? strlen(pTopModule) : 0) + strlen(pFileTemp) + 200;
    pCommand = ABC_ALLOC( char, nCommand );
    sprintf( pCommand, "%s -qp \"read_verilog %s%s %s%s; hierarchy %s%s; %sproc; memory -nomap; memory_map; write_rtlil %s\"",
        Wln_GetYosysName(), 
        pDefines   ? "-D"       : "",
        pDefines   ? pDefines   : "",
        fSVlog     ? "-sv "     : "",
        pFileNames,
        pTopModule ? "-top "    : "", 
        pTopModule ? pTopModule : "", 
        fCollapse  ? "flatten; ": "",
        pFileTemp );
    if ( fVerbose )
        printf( "%s\n", pCommand );
    if ( !Wln_ConvertToRtl(pCommand, pFileTemp) )
    {
        ABC_FREE( pCommand );
        ABC_FREE( pFileNames );
        return NULL;
    }
    ABC_FREE( pCommand );
    ABC_FREE( pFileNames );
    pNtk = Rtl_LibReadFile( pFileTemp, ppFileNames[0] );
    if ( pNtk == NULL )
    {
        printf( "Dumped the design into file \"%s\".\n", pFileTemp );
        return NULL;
    }
    Rtl_NtkCleanFile( pFileTemp );
    unlink( pFileTemp );
    return pNtk;
}
Gia_Man_t * Wln_BlastSystemVerilog( char ** ppFileNames, int nFileNames, char * pTopModule, char * pDefines, int fSkipStrash, int fInvert, int fTechMap, int fLibInDir, int fSetUndef, int fVerbose )
{
    Gia_Man_t * pGia = NULL;
    char * pFileNames, * pCommand;
    char * pFileTemp, * pFileBase;
    int fRtlil = nFileNames == 1 && strstr(ppFileNames[0], ".rtl") != NULL;
    int fSVlog = Wln_FileNamesHasSv(ppFileNames, nFileNames);
    int nCommand;
    pFileBase = pTopModule ? Abc_UtilStrsav(pTopModule) :
        Extra_FileNameGeneric( Extra_FileNameWithoutPath(ppFileNames[0]) );
    pFileTemp = ABC_ALLOC( char, strlen(pFileBase) + 5 );
    sprintf( pFileTemp, "%s.aig", pFileBase );
    ABC_FREE( pFileBase );
    pFileNames = Wln_FileNamesJoin( ppFileNames, nFileNames );
    nCommand = strlen(Wln_GetYosysName()) + strlen(pFileNames) + (pDefines ? strlen(pDefines) : 0) + (pTopModule ? strlen(pTopModule) : 0) + strlen(pFileTemp) + 500;
    pCommand = ABC_ALLOC( char, nCommand );
    sprintf( pCommand, "%s -qp \"%s %s%s %s%s; hierarchy %s%s; flatten; proc; opt; async2sync; opt; setundef -undriven -zero; %s%smemory -nomap; memory_map; dffunmap; opt_clean; opt_expr; %saigmap; write_aiger -symbols %s\"",
        Wln_GetYosysName(), 
        fRtlil ? "read_rtlil"   : "read_verilog",
        pDefines  ? "-D"        : "",
        pDefines  ? pDefines    : "",
        fSVlog    ? "-sv "      : "",
        pFileNames,
        pTopModule ? "-top "    : "-auto-top",
        pTopModule ? pTopModule : "", 
        fTechMap ? (fLibInDir ? "techmap -map techmap.v; " : "techmap; ") : "",
        fSetUndef ? "setundef -init -zero; " : "",
        nFileNames > 1 ? "delete t:\\$scopeinfo; " : "",
        pFileTemp );
    if ( fVerbose )
        printf( "%s\n", pCommand );
    if ( !Wln_ConvertToRtl(pCommand, pFileTemp) )
    {
        ABC_FREE( pCommand );
        ABC_FREE( pFileNames );
        ABC_FREE( pFileTemp );
        return NULL;
    }
    ABC_FREE( pCommand );
    ABC_FREE( pFileNames );
    pGia = Gia_AigerRead( pFileTemp, 0, fSkipStrash, 0 );
    if ( pGia == NULL )
    {
        printf( "Converting to AIG has failed.\n" );
        ABC_FREE( pFileTemp );
        return NULL;
    }
    ABC_FREE( pGia->pName );
    pGia->pName = pTopModule ? Abc_UtilStrsav(pTopModule) :
        Extra_FileNameGeneric( Extra_FileNameWithoutPath(ppFileNames[0]) );
    unlink( pFileTemp );
    ABC_FREE( pFileTemp );
    // complement the outputs
    if ( fInvert )
    {
        Gia_Obj_t * pObj; int i;
        Gia_ManForEachPo( pGia, pObj, i )
            Gia_ObjFlipFaninC0( pObj );
    }
    return pGia;
}
Abc_Ntk_t * Wln_ReadMappedSystemVerilog( char ** ppFileNames, int nFileNames, char * pTopModule, char * pDefines, char * pLibrary, int fVerbose )
{
    Abc_Ntk_t * pNtk = NULL;
    char * pFileNames, * pCommand;
    char * pFileTemp = "_temp_.blif";
    int fSVlog = Wln_FileNamesHasSv(ppFileNames, nFileNames);
    int nCommand;
    pFileNames = Wln_FileNamesJoin( ppFileNames, nFileNames );
    nCommand = strlen(Wln_GetYosysName()) + strlen(pLibrary) + strlen(pFileNames) + (pDefines ? strlen(pDefines) : 0) + 2 * (pTopModule ? strlen(pTopModule) : 0) + strlen(pFileTemp) + 300;
    pCommand = ABC_ALLOC( char, nCommand );
    sprintf( pCommand, "%s -qp \"read_liberty -lib %s; read %s %s%s %s; hierarchy %s%s; flatten; proc; memory -nomap; memory_map; write_blif %s%s -impltf -gates %s\"",
        Wln_GetYosysName(),
        pLibrary,
        fSVlog    ? "-sv "      : "-vlog95",
        pDefines  ? "-D"        : "",
        pDefines  ? pDefines    : "",
        pFileNames,
        pTopModule ? "-top "    : "-auto-top",
        pTopModule ? pTopModule : "",
        pTopModule ? "-top "    : "",
        pTopModule ? pTopModule : "",
        pFileTemp );
    if ( fVerbose )
        printf( "%s\n", pCommand );
    if ( !Wln_ConvertToRtl(pCommand, pFileTemp) )
    {
        ABC_FREE( pCommand );
        ABC_FREE( pFileNames );
        return NULL;
    }
    ABC_FREE( pCommand );
    ABC_FREE( pFileNames );
    pCommand = ABC_ALLOC( char, strlen(pLibrary) + 20 );
    sprintf( pCommand, "read_lib %s", pLibrary );
    if ( Cmd_CommandExecute( Abc_FrameReadGlobalFrame(), pCommand ) )
    {
        fprintf( stdout, "Cannot execute ABC command \"%s\".\n", pCommand );
        ABC_FREE( pCommand );
        unlink( pFileTemp );
        return NULL;
    }
    ABC_FREE( pCommand );
    pNtk = Io_Read( pFileTemp, IO_FILE_BLIF, 1, 0 );
    if ( pNtk == NULL )
    {
        printf( "Reading mapped BLIF from file \"%s\" has failed.\n", pFileTemp );
        return NULL;
    }
    if ( pTopModule ) {
        ABC_FREE( pNtk->pName );
        pNtk->pName = Abc_UtilStrsav(pTopModule);
    }
    unlink( pFileTemp );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
