/**CFile****************************************************************

  FileName    [cmdPlugin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Integrating external binary.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 29, 2010.]

  Revision    [$Id: cmdPlugin.c,v 1.00 2010/09/29 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifdef WIN32
#include <io.h> 
#include <process.h> 
#else
#include <unistd.h>
#endif

#include "src/base/abc/abc.h"
#include "src/base/main/mainInt.h"
#include "cmd.h"
#include "cmdInt.h"
#include "src/misc/util/utilSignal.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*

-------- Original Message --------
Subject:     ABC/ZZ integration
Date:     Wed, 29 Sep 2010 00:34:32 -0700
From:     Niklas Een <niklas@een.se>
To:     Alan Mishchenko <alanmi@EECS.Berkeley.EDU>

Hi Alan,

Since the interface is file-based, it is important that we generate 
good, unique filenames (we may run multiple instances of ABC in the 
same directory), so I have attached some portable code for doing that 
(tmpFile.c). You can integrate it appropriately.

This is how my interface is meant to work:

(1) As part of your call to Bip, give it first argument "-abc". 
    This will alter Bip's behavior slightly.

(2) To list the commands, call 'bip -list-commands'. 
    My commands begin with a comma (so that's my prefix).

(3) All commands expect an input file and an output file. 
    The input file should be in AIGER format. 
    The output will be a text file. 
    Example:
       bip -input=tmp.aig -output=tmp.out ,pdr -check -prop=5

    So you just auto-generate the two temporary files (output file is 
    closed and left empty) and stitch the ABC command line at the end. 
    All you need to check for is if the ABC line begins with a comma.

(4) The result written to the output file will contain a number 
    of object. Each object is on a separate line of the form:

    <object name>: <object data>

That is: name, colon, space, data, newline. If you see a name you don't 
recognize, just skip that line (so you will ignore future extensions by me). 
I currently define the following objects:

    result:
    counter-example:
    proof-invariant:
    bug-free-depth:
    abstraction:
  
"result:" is one of "proved", "failed", "undetermined" (=reached resource limit), "error" 
(only used by the abstraction command, and only if resource limit was so tight that the 
abstraction was still empty -- no abstraction is returned in this special case).

"counter-example:" -- same format as before

"proof-invariant:" contains an text-encoded single-output AIG. If you want 
you can parse it and validate the invariant.

"bug-free-depth:" the depth up to which the procedure has checked for counter-example. 
Starts at -1 (not even the initial states have been verified).

"abstraction:" -- same format as before

(5) I propose that you add a command "load_plugin <path/binary>". That way Bob can put 
Bip where ever he likes and just modify his abc_rc file.

The intention is that ABC can read this file and act on it without knowing what 
particular command was used. If there is an abstraction, you will always apply it. 
If there is a "bug-free-depth" you will store that data somewhere so that Bob can query 
it through the Python interface, and so on. If we need different actions for different 
command, then we add a new object for the new action.

// N.

*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_GetBinaryName( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pTemp;
    int i;
    Vec_PtrForEachEntry( char *, pAbc->vPlugInComBinPairs, pTemp, i )
    {
        i++;
        if ( strcmp( pTemp, argv[0] ) == 0 )
            return (char *)Vec_PtrEntry( pAbc->vPlugInComBinPairs, i );
    }
    assert( 0 );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Abc_ManReadFile( char * pFileName )
{
    FILE * pFile;
    Vec_Str_t * vStr;
    int c;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    vStr = Vec_StrAlloc( 100 );
    while ( (c = fgetc(pFile)) != EOF )
        Vec_StrPush( vStr, (char)c );
    Vec_StrPush( vStr, '\0' );
    fclose( pFile );
    return vStr;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_ManReadBinary( char * pFileName, char * pToken )
{
    Vec_Int_t * vMap = NULL;
    Vec_Str_t * vStr;
    char * pStr;
    int i, Length;
    vStr = Abc_ManReadFile( pFileName );
    if ( vStr == NULL )
        return NULL;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
    {
        pStr  += strlen( pToken );
        vMap   = Vec_IntAlloc( 100 );
        Length = strlen( pStr );
        for ( i = 0; i < Length; i++ )
        {
            if ( pStr[i] == '0' || pStr[i] == '?' )
                Vec_IntPush( vMap, 0 );
            else if ( pStr[i] == '1' )
                Vec_IntPush( vMap, 1 );
            if ( ('a' <= pStr[i] && pStr[i] <= 'z') || 
                 ('A' <= pStr[i] && pStr[i] <= 'Z') )
                break;
        }
    }
    Vec_StrFree( vStr );
    return vMap;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ManReadInteger( char * pFileName, char * pToken )
{
    int Result = -1;
    Vec_Str_t * vStr;
    char * pStr;
    vStr = Abc_ManReadFile( pFileName );
    if ( vStr == NULL )
        return -1;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
        Result = atoi( pStr + strlen(pToken) );
    Vec_StrFree( vStr );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ManReadStatus( char * pFileName, char * pToken )
{
    int Result = -1;
    Vec_Str_t * vStr;
    char * pStr;
    vStr = Abc_ManReadFile( pFileName );
    if ( vStr == NULL )
        return -1;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
    {
        if ( strncmp(pStr+8, "proved", 6) == 0 )
            Result = 1; 
        else if ( strncmp(pStr+8, "failed", 6) == 0 )
            Result = 0; 
    }
    Vec_StrFree( vStr );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Work-around to insert 0s for PIs without fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_ManExpandCex( Gia_Man_t * pGia, Vec_Int_t * vCex )
{
    Vec_Int_t * vCexNew;
    Gia_Obj_t * pObj;
    int i, k;

    // start with register outputs
    vCexNew = Vec_IntAlloc( Vec_IntSize(vCex) );
    Gia_ManForEachRo( pGia, pObj, i )
        Vec_IntPush( vCexNew, 0 );

    ABC_FREE( pGia->pRefs );
    Gia_ManCreateRefs( pGia );
    k = Gia_ManRegNum( pGia );
    while ( 1 )
    {
        Gia_ManForEachPi( pGia, pObj, i )
        {
            if ( Gia_ObjRefs(pGia, pObj) == 0 )
                Vec_IntPush( vCexNew, 0 );
            else
            {
                if ( k == Vec_IntSize(vCex) )
                    break;
                Vec_IntPush( vCexNew, Vec_IntEntry(vCex, k++) );
            }
        }
        if ( k == Vec_IntSize(vCex) )
            break;
    }
    return vCexNew;
}

/**Function*************************************************************

  Synopsis    [Procedure to convert the AIG from text into binary form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned textToBin(char* text, unsigned long text_sz)
{
    char*       dst = text;
    const char* src = text;
    unsigned sz, i;
    sscanf(src, "%lu ", &sz);
    while(*src++ != ' ');
    for ( i = 0; i < sz; i += 3 )
    {
        dst[0] = (char)( (unsigned)src[0] - '0')       | (((unsigned)src[1] - '0') << 6);
        dst[1] = (char)(((unsigned)src[1] - '0') >> 2) | (((unsigned)src[2] - '0') << 4);
        dst[2] = (char)(((unsigned)src[2] - '0') >> 4) | (((unsigned)src[3] - '0') << 2);
        src += 4;
        dst += 3;
    }
    return sz;
}

/**Function*************************************************************

  Synopsis    [Derives AIG from the text string in the file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_ManReadAig( char * pFileName, char * pToken )
{
    Gia_Man_t * pGia = NULL;
    unsigned nBinaryPart;
    Vec_Str_t * vStr;
    char * pStr, * pEnd;
    vStr = Abc_ManReadFile( pFileName );
    if ( vStr == NULL )
        return NULL;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
    {
        // skip token
        pStr += strlen(pToken);
        // skip spaces
        while ( *pStr == ' ' )
            pStr++;
        // set the end at newline
        for ( pEnd = pStr; *pEnd; pEnd++ )
            if ( *pEnd == '\r' || *pEnd == '\n' )
            {
                *pEnd = 0;
                break;
            }
        // convert into binary AIGER
        nBinaryPart = textToBin( pStr, strlen(pStr) );
        // dump it into file
        if ( 0 )
        {
            FILE * pFile = fopen( "test.aig", "wb" );
            fwrite( pStr, 1, nBinaryPart, pFile );
            fclose( pFile );
        }
        // derive AIG
        pGia = Gia_ReadAigerFromMemory( pStr, nBinaryPart, 0 ); 
    }
    Vec_StrFree( vStr );
    return pGia;

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cmd_CommandAbcPlugIn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileIn, * pFileOut;
    char * pFileNameBinary;
    Vec_Str_t * vCommand;
    Vec_Int_t * vCex;
    FILE * pFile;
    Gia_Man_t * pGia;
    int i, fd, clk;
    int fLeaveFiles;
/*
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Current network does not exist\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash( pNtk) )
    {
        Abc_Print( -1, "The current network is not an AIG. Cannot continue.\n" );
        return 1;
    }
*/

    if ( pAbc->pGia == NULL )
    {
        if (argc == 2 && strcmp(argv[1], "-h") == 0)
        {
            // Run command to produce help string:
            vCommand = Vec_StrAlloc( 100 );
            pFileNameBinary = Abc_GetBinaryName( pAbc, argc, argv );
            Vec_StrAppend( vCommand, pFileNameBinary );
            Vec_StrAppend( vCommand, " -abc " );
            Vec_StrAppend( vCommand, argv[0] );
            Vec_StrAppend( vCommand, " -h" );
            Vec_StrPush( vCommand, 0 );
            Util_SignalSystem( Vec_StrArray(vCommand) );
            Vec_StrFree( vCommand );
        }
        else
        {
            Abc_Print( -1, "Current AIG does not exist (try command &ps).\n" );
        }
        return 1;
    }

    // check if there is the binary
    pFileNameBinary = Abc_GetBinaryName( pAbc, argc, argv );
    if ( (pFile = fopen( pFileNameBinary, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot run the binary \"%s\".\n\n", pFileNameBinary );
        return 1;
    }
    fclose( pFile );

    // create temp file
    fd = Util_SignalTmpFile( "__abctmp_", ".aig", &pFileIn );
    if ( fd == -1 )
    {
        Abc_Print( -1, "Cannot create a temporary file.\n" );
        return 1;
    }
#ifdef WIN32
    _close( fd );
#else
    close( fd );
#endif

    // create temp file
    fd = Util_SignalTmpFile( "__abctmp_", ".out", &pFileOut );
    if ( fd == -1 )
    {
        ABC_FREE( pFileIn );
        Abc_Print( -1, "Cannot create a temporary file.\n" );
        return 1;
    }
#ifdef WIN32
    _close( fd );
#else
    close( fd );
#endif


    // write current network into a file
/*
    {
        extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
        Aig_Man_t * pAig;
        pAig = Abc_NtkToDar( pNtk, 0, 1 );
        Ioa_WriteAiger( pAig, pFileIn, 0, 0 );
        Aig_ManStop( pAig );
    }
*/ 
    // check what to do with the files
    fLeaveFiles = 0;
    if ( strcmp( argv[argc-1], "!" ) == 0 )
    {
        Abc_Print( 0, "Input file \"%s\" and output file \"%s\" are not deleted.\n", pFileIn, pFileOut );
        fLeaveFiles = 1;
        argc--;
    }

    // create input file
    Gia_WriteAiger( pAbc->pGia, pFileIn, 0, 0 );

    // create command line
    vCommand = Vec_StrAlloc( 100 );
    Vec_StrAppend( vCommand, pFileNameBinary );
    // add input/output file
    Vec_StrAppend( vCommand, " -abc" );
//    Vec_StrAppend( vCommand, " -input=C:/_projects/abc/_TEST/hwmcc/139442p0.aig" );
    Vec_StrAppend( vCommand, " -input=" );
    Vec_StrAppend( vCommand, pFileIn );
    Vec_StrAppend( vCommand, " -output=" );
    Vec_StrAppend( vCommand, pFileOut );
    // add other arguments
    for ( i = 0; i < argc; i++ )
    {
        Vec_StrAppend( vCommand, " " );
        Vec_StrAppend( vCommand, argv[i] );
    }
    Vec_StrPush( vCommand, 0 );

    // run the command line
//printf( "Running command line: %s\n", Vec_StrArray(vCommand) ); 

    clk = clock();
    if ( Util_SignalSystem( Vec_StrArray(vCommand) ) )
    {
        Abc_Print( -1, "The following command has returned non-zero exit status:\n" );
        Abc_Print( -1, "\"%s\"\n", Vec_StrArray(vCommand) );
        return 1;
    }
    clk = clock() - clk;
    Vec_StrFree( vCommand );

    // check if the output file exists
    if ( (pFile = fopen( pFileOut, "r" )) == NULL )
    {
        Abc_Print( -1, "There is no output file \"%s\".\n", pFileOut );
        return 1;
    }
    fclose( pFile );

    // process the output
    if ( Extra_FileSize(pFileOut) > 0 )
    {
        // get status
        pAbc->Status  = Abc_ManReadStatus( pFileOut, "result:" );
        // get bug-free depth
        pAbc->nFrames = Abc_ManReadInteger( pFileOut, "bug-free-depth:" );
        // get abstraction
        pAbc->pGia->vFlopClasses = Abc_ManReadBinary( pFileOut, "abstraction:" );
        // get counter-example
        vCex = Abc_ManReadBinary( pFileOut, "counter-example:" );
        if ( vCex ) 
        {
            int nFrames, nRemain;

            nFrames = (Vec_IntSize(vCex) - Gia_ManRegNum(pAbc->pGia)) / Gia_ManPiNum(pAbc->pGia);
            nRemain = (Vec_IntSize(vCex) - Gia_ManRegNum(pAbc->pGia)) % Gia_ManPiNum(pAbc->pGia);
            if ( nRemain != 0 )
            {   
                Vec_Int_t * vTemp;
                Abc_Print( 1, "Adjusting counter-example by adding zeros for PIs without fanout.\n" );
                // expand the counter-example to include PIs without fanout
                vCex = Abc_ManExpandCex( pAbc->pGia, vTemp = vCex );
                Vec_IntFree( vTemp );
            }

            nFrames = (Vec_IntSize(vCex) - Gia_ManRegNum(pAbc->pGia)) / Gia_ManPiNum(pAbc->pGia);
            nRemain = (Vec_IntSize(vCex) - Gia_ManRegNum(pAbc->pGia)) % Gia_ManPiNum(pAbc->pGia);
            if ( nRemain != 0 )
                Abc_Print( 1, "Counter example has a wrong length.\n" );
            else
            {
                Abc_Print( 1, "Problem is satisfiable. Found counter-example in frame %d.  ", nFrames-1 );
                Abc_PrintTime( 1, "Time", clk );
                ABC_FREE( pAbc->pCex );
                pAbc->pCex = Abc_CexCreate( Gia_ManRegNum(pAbc->pGia), Gia_ManPiNum(pAbc->pGia), Vec_IntArray(vCex), nFrames-1, 0, 0 );

//                Abc_CexPrint( pAbc->pCex );

//                if ( !Gia_ManVerifyCex( pAbc->pGia, pAbc->pCex, 0 ) )
//                    Abc_Print( 1, "Generated counter-example is INVALID.\n" );

                // remporary work-around to detect the output number - October 18, 2010
                pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pAbc->pGia, pAbc->pCex, 0 );
                if ( pAbc->pCex->iPo == -1 )
                {
                    Abc_Print( 1, "Generated counter-example is INVALID.\n" );
                    ABC_FREE( pAbc->pCex );
                }
                else
                {
                    Abc_Print( 1, "Returned counter-example successfully verified in ABC.\n" );
                }
            }
            Vec_IntFreeP( &vCex );
        }
        // get AIG if present
        pGia = Abc_ManReadAig( pFileOut, "aig:" );
        if ( pGia != NULL )
        {
            Gia_ManStopP( &pAbc->pGia );
            pAbc->pGia = pGia;                
        }
    }    

    // clean up
    Util_SignalTmpFileRemove( pFileIn, fLeaveFiles );
    Util_SignalTmpFileRemove( pFileOut, fLeaveFiles );
    
    ABC_FREE( pFileIn );
    ABC_FREE( pFileOut );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cmd_CommandAbcLoadPlugIn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    char pBuffer[1000];
    char * pCommandLine;
    char * pTempFile;
    char * pStrDirBin, * pStrSection;
    int fd, RetValue;

    if ( argc != 3 )
    {
        Abc_Print( -1, "Wrong number of arguments.\n" );
        goto usage;
    }
    // collect arguments
    pStrDirBin  = argv[argc-2];
    pStrSection = argv[argc-1];

    // check if the file exists
    if ( (pFile = fopen( pStrDirBin, "r" )) == NULL )
    {
//        Abc_Print( -1, "Cannot run the binary \"%s\".\n", pStrDirBin );
//        goto usage;
        return 0;
    }
    fclose( pFile );

    // create temp file
    fd = Util_SignalTmpFile( "__abctmp_", ".txt", &pTempFile );
    if ( fd == -1 )
    {
        Abc_Print( -1, "Cannot create a temporary file.\n" );
        goto usage;
    }
#ifdef WIN32
    _close( fd );
#else
    close( fd );
#endif

    // get command list
    pCommandLine = ABC_ALLOC( char, 100 + strlen(pStrDirBin) + strlen(pTempFile) );
//    sprintf( pCommandLine, "%s -abc -list-commands > %s", pStrDirBin, pTempFile );
    sprintf( pCommandLine, "%s -abc -list-commands > %s", pStrDirBin, pTempFile );
    RetValue = Util_SignalSystem( pCommandLine );
    if ( RetValue == -1 )
    {
        Abc_Print( -1, "Command \"%s\" did not succeed.\n", pCommandLine );
        ABC_FREE( pCommandLine );
        ABC_FREE( pTempFile );
        goto usage;
    }
    ABC_FREE( pCommandLine );

    // create commands
    pFile = fopen( pTempFile, "r" );
    if ( pFile == NULL )
    {
        Abc_Print( -1, "Cannot open file with the list of commands.\n" );
        ABC_FREE( pTempFile );
        goto usage;
    }
    while ( fgets( pBuffer, 1000, pFile ) != NULL )
    {
        if ( pBuffer[strlen(pBuffer)-1] == '\n' )
            pBuffer[strlen(pBuffer)-1] = 0;
        Cmd_CommandAdd( pAbc, pStrSection, pBuffer, Cmd_CommandAbcPlugIn, 1 );
//        plugin_commands.push(Pair(cmd_name, binary_name));
        Vec_PtrPush( pAbc->vPlugInComBinPairs, Extra_UtilStrsav(pBuffer) );
        Vec_PtrPush( pAbc->vPlugInComBinPairs, Extra_UtilStrsav(pStrDirBin) );
        printf( "Creating command %s with binary %s\n", pBuffer, pStrDirBin );
    }
    fclose( pFile );
    Util_SignalTmpFileRemove( pTempFile, 0 );
    ABC_FREE( pTempFile );
    return 0;
usage:
    Abc_Print( -2, "usage: load_plugin <plugin_dir\\binary_name> <section_name>\n" );
    Abc_Print( -2, "\t        loads external binary as a plugin\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

