/**CFile****************************************************************

  FileName    [abcGen.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Circuit generators and development drivers.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandTestRand               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRunGen                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRunScript              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGen                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGenTF                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGenAT                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGenPop                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGenFsm                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestColor              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTest                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSymFun                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCubeEnum               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPathEnum               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFunEnum                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SymFun             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Mesh               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenLutCas          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Gen                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenHie             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenRel             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenMux             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Test               ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandNChooseK               ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

/**Function*************************************************************

  Synopsis    [Registers circuit generators and development drivers commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitGen( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "testrand",      Abc_CommandTestRand,         0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "rungen",        Abc_CommandRunGen,           0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "runscript",     Abc_CommandRunScript,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "gen",           Abc_CommandGen,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "gentf",         Abc_CommandGenTF,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "genat",         Abc_CommandGenAT,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "genpop",        Abc_CommandGenPop,           0 );
    Cmd_CommandAdd( pAbc, "Various",      "genfsm",        Abc_CommandGenFsm,           0 );
    Cmd_CommandAdd( pAbc, "Various",      "testcolor",     Abc_CommandTestColor,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "test",          Abc_CommandTest,             0 );
//    Cmd_CommandAdd( pAbc, "Various",      "qbf_solve",     Abc_CommandTest,               0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "symfun",        Abc_CommandSymFun,           0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cubeenum",      Abc_CommandCubeEnum,         0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "pathenum",      Abc_CommandPathEnum,         0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "funenum",       Abc_CommandFunEnum,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&symfun",       Abc_CommandAbc9SymFun,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mesh",         Abc_CommandAbc9Mesh,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&genlutcas",    Abc_CommandAbc9GenLutCas,    0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "nck",           Abc_CommandNChooseK,                   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gen",          Abc_CommandAbc9Gen,                    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gen_hie",      Abc_CommandAbc9GenHie,                 0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&genrel",       Abc_CommandAbc9GenRel,                 0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&genmux",       Abc_CommandAbc9GenMux,                 0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&test",         Abc_CommandAbc9Test,                   0 );
}

////////////////////////////////////////////////////////////////////////
///                       FUNCTION DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestRand( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkRandFile( char * pFileName, int nVars, int nFuncs, int nMints );
    int c, nVars = 0, nFuncs = 0, nMints = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NFMvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFuncs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMints = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 1,"Input file is not given.\n" );
        return 0;
    }
    Abc_NtkRandFile( argv[globalUtilOptind], nVars, nFuncs, nMints );
    return 0;

usage:
    Abc_Print( -2, "usage: testrand [-NFMvh] <file>\n" );
    Abc_Print( -2, "\t           generates truth tables and writes them into a file\n" );
    Abc_Print( -2, "\t-N <num> : the number of input variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-F <num> : the number of random functions to generate [default = %d]\n", nFuncs );
    Abc_Print( -2, "\t-M <num> : the number of positive minterms in the random function [default = %d]\n", nMints );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file>   : file to write the truth tables to\n");    
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRunGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Acb_NtkRunGen( int nInputs, int nMints, int nFuncs, int Seed, int fVerbose, char * pScript );
    int c, nInputs = 10, nMints = 10, nFuncs = 10, Seed = 0, fVerbose = 0; char * pScript = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IMRSCvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMints = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nFuncs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a script.\n" );
                goto usage;
            }
            pScript = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pScript == NULL ) 
    {
        Abc_Print( -1, "Command line switch \"-C\" should be specified and followed by a string.\n" );
        goto usage;        
    }
    Acb_NtkRunGen( nInputs, nMints, nFuncs, Seed, fVerbose, pScript );
    return 0;

usage:
    Abc_Print( -2, "usage: rungen [-IMRS num] [-C script] [-vh]\n" );
    Abc_Print( -2, "\t           running the script on a set of randomly generated functions\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", nInputs );
    Abc_Print( -2, "\t-M <num> : the number of positive minterms in the random function [default = %d]\n", nMints );
    Abc_Print( -2, "\t-R <num> : the number of random functions to try [default = %d]\n", nFuncs );
    Abc_Print( -2, "\t-S <num> : the random seed [default = %d]\n", Seed );
    Abc_Print( -2, "\t-C <num> : the script to apply [default = provided by the user]\n" );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRunScript( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, nIters = 10, nBeg = 1, nAdd = 1, fReverse = 0, fVerbose = 0; char * pScript = NULL, * pSpot = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IBASrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBeg = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a script.\n" );
                goto usage;
            }
            pScript = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            fReverse ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pScript == NULL ) 
    {
        Abc_Print( -1, "Command line switch \"-S\" should be specified and followed by a string.\n" );
        goto usage;        
    }
    pSpot = strstr( pScript, "*" );
    if ( pSpot == NULL ) 
    {
        abctime clkTotal = Abc_Clock();
        for ( c = 0; c < nIters; c++ )
        {
            if ( fVerbose )
                printf( "ITERATION %3d : %s\n", c, pScript );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) ) {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
                goto usage;
            }        
        }
        printf( "Finished iterating script %d times.  ", nIters );
        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
        return 0;    
    }
    else
    {
        abctime clkTotal = Abc_Clock();
        assert( *pSpot == '*' );
        for ( c = 0; c < nIters; c++ )
        {
            char pCommLine[1000] = {0};
            char pNumber[10] = {0};
            sprintf( pNumber, "%d", fReverse ? nBeg - c*nAdd : nBeg + c*nAdd );
            strcpy( pCommLine, pScript );
            pCommLine[(int)(pSpot - pScript)] = 0;
            strcat( pCommLine, pNumber );
            strcat( pCommLine, pSpot+1 );
            if ( fVerbose )
                printf( "ITERATION %3d : %s\n", c, pCommLine );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pCommLine) ) {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pCommLine );
                goto usage;
            }        
        }
        printf( "Finished iterating script %d times.  ", nIters );
        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: runscript [-IBA num] [-S str] [-rvh]\n" );
    Abc_Print( -2, "\t           running the script with different values\n" );
    Abc_Print( -2, "\t-I <num> : the number of iterations [default = %d]\n", nIters );
    Abc_Print( -2, "\t-B <num> : the starting number [default = %d]\n", nBeg );
    Abc_Print( -2, "\t-A <num> : the increment added in each iteration [default = %d]\n", nAdd );
    Abc_Print( -2, "\t-S <str> : the script to iterate [default = none]\n" );
    Abc_Print( -2, "\t-r       : toggle reversing the order of counting [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nVars;    // the number of variables
    int nArgs;    // the number of arguments
    int nLutSize = -1; // the size of LUTs
    int nLuts = -1;    // the number of LUTs
    int fAdder;
    int fAdderTree;
    int fSorter;
    int fMesh;
    int fMulti;
    int fBooth;
    int fFpga;
    int fOneHot;
    int fRandom;
    int fGraph;
    int fVerbose;
    char * FileName;
    char Command[1000];
    extern void Abc_GenAdder( char * pFileName, int nVars );
    extern void Abc_GenSorter( char * pFileName, int nVars );
    extern void Abc_GenMesh( char * pFileName, int nVars );
    extern void Abc_GenMulti( char * pFileName, int nVars );
    extern void Abc_GenBooth( char * pFileName, int nVars );
    extern void Abc_GenFpga( char * pFileName, int nLutSize, int nLuts, int nVars );
    extern void Abc_GenOneHot( char * pFileName, int nVars );
    extern void Abc_GenRandom( char * pFileName, int nPis );
    extern void Abc_GenGraph( char * pFileName, int nPis );
    extern void Abc_GenAdderTree( char * pFileName, int nArgs, int nBits );

    // set defaults
    nVars = 8;
    nArgs = 8;
    fAdder = 0;
    fAdderTree = 0;
    fSorter = 0;
    fMesh = 0;
    fMulti = 0;
    fBooth = 0;
    fFpga = 0;
    fOneHot = 0;
    fRandom = 0;
    fGraph = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NAKLatsembfnrgvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nArgs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nArgs < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLuts < 0 )
                goto usage;
            break;
        case 'a':
            fAdder ^= 1;
            break;
        case 't':
            fAdderTree ^= 1;
            break;
        case 's':
            fSorter ^= 1;
            break;
        case 'e':
            fMesh ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 'b':
            fBooth ^= 1;
            break;
        case 'f':
            fFpga ^= 1;
            break;
        case 'n':
            fOneHot ^= 1;
            break;
        case 'r':
            fRandom ^= 1;
            break;
        case 'g':
            fGraph ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }
    if ( nVars < 1 )
    {
        Abc_Print( -1, "The number of variables should be a positive integer.\n" );
        return 0;
    }
    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( fAdder )
        Abc_GenAdder( FileName, nVars );
    else if ( fSorter )
        Abc_GenSorter( FileName, nVars );
    else if ( fMesh )
        Abc_GenMesh( FileName, nVars );
    else if ( fMulti )
        Abc_GenMulti( FileName, nVars );
    else if ( fBooth )
        Abc_GenBooth( FileName, nVars );
    else if ( fFpga )
        Abc_GenFpga( FileName, nLutSize, nLuts, nVars );
//        Abc_GenFpga( FileName, 2, 2, 3 );
//        Abc_GenFpga( FileName, 3, 2, 5 );
    else if ( fOneHot )
        Abc_GenOneHot( FileName, nVars );
    else if ( fRandom )
        Abc_GenRandom( FileName, nVars );
    else if ( fGraph )
        Abc_GenGraph( FileName, nVars );
    else if ( fAdderTree )
    {
        printf( "Generating adder tree with %d arguments and %d bits.\n", nArgs, nVars );
        Abc_GenAdderTree( FileName, nArgs, nVars );
        sprintf( Command, "%%read %s; %%blast; &put", FileName );
        Cmd_CommandExecute( pAbc, Command );
        return 0;
    }
    else
    {
        Abc_Print( -1, "Type of circuit is not specified.\n" );
        return 0;
    }
    // read the file just produced
    sprintf(Command, "read %s", FileName );
    Cmd_CommandExecute( pAbc, Command );
    return 0;

usage:
    Abc_Print( -2, "usage: gen [-NAKL num] [-atsembfnrgvh] <file>\n" );
    Abc_Print( -2, "\t         generates simple circuits\n" );
    Abc_Print( -2, "\t-N num : the number of variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-A num : the number of arguments (for adder tree) [default = %d]\n", nArgs );
    Abc_Print( -2, "\t-K num : the LUT size (to be used with switch -f) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-L num : the LUT count (to be used with switch -f) [default = %d]\n", nLuts );
    Abc_Print( -2, "\t-a     : generate ripple-carry adder [default = %s]\n", fAdder? "yes": "no" );
    Abc_Print( -2, "\t-t     : generate an adder tree [default = %s]\n", fAdderTree? "yes": "no" );
    Abc_Print( -2, "\t-s     : generate a sorter [default = %s]\n", fSorter? "yes": "no" );
    Abc_Print( -2, "\t-e     : generate a mesh [default = %s]\n", fMesh? "yes": "no" );
    Abc_Print( -2, "\t-m     : generate a multiplier [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-b     : generate a signed Booth multiplier [default = %s]\n", fBooth? "yes": "no" );
    Abc_Print( -2, "\t-f     : generate a LUT FPGA structure [default = %s]\n", fFpga? "yes": "no" );
    Abc_Print( -2, "\t-g     : generate a graph structure [default = %s]\n", fGraph? "yes": "no" );
    Abc_Print( -2, "\t-n     : generate one-hotness conditions [default = %s]\n", fOneHot? "yes": "no" );
    Abc_Print( -2, "\t-r     : generate random single-output function [default = %s]\n", fRandom? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : output file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGenTF( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_GenThresh( char * pFileName, int nBits, Vec_Int_t * vNums, int nLutSize, char * pArch );
    int c, nBits = 0, nLutSize = -1, fVerbose = 0, nSum = 0;
    char Command[1000], * pFileName = "out.blif", * pArch = NULL;
    Vec_Int_t * vNums = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WKAvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nBits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBits < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pArch = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind )
        goto usage;
    if ( nBits == 0 )
    {
        Abc_Print( -1, "Bit-width should be specified.\n" );
        return 0;        
    }
    if ( nLutSize != -1 && nLutSize != 4 && nLutSize != 6 )
    {
        Abc_Print( -1, "LUT size %d is not supported.\n", nLutSize );
        return 0;
    }
    if ( pArch )
    {
        int Counts[2] = {0};
        for ( c = 0; c < strlen(pArch); c++ )
            if ( pArch[c] == '(' )
                Counts[0]++;
            else if ( pArch[c] == ')' )
                Counts[1]++;
            else if ( pArch[c] >= '1' && pArch[c] <= '9' )
                nSum += pArch[c] - '0';
            else if ( pArch[c] >= 'A' && pArch[c] <= 'Z' )
                nSum += pArch[c] - 'A' + 10;
            else {
                Abc_Print( -1, "Architecture description contains a wrong symbol (%c).\n", pArch[c] );
                return 0;            
            }
        if ( Counts[0] != Counts[1] )
        {
            Abc_Print( -1, "Mismatching number of opening and closing parentheses (%d and %d).\n", Counts[0], Counts[1] );
            return 0; 
        }
    }
    vNums = Vec_IntAlloc( argc );
    for ( c = globalUtilOptind; c < argc; c++ )
        Vec_IntPush( vNums, atoi(argv[c]) );
    if ( Vec_IntSize(vNums) < 3 ) {
        Abc_Print( -1, "Expecting that at least two weights and a threshold are specified on the command line.\n" );
        Vec_IntFree( vNums );
        return 0; 
    }
    if ( pArch && nSum != Vec_IntSize(vNums)-1 ) {
        Abc_Print( -1, "The architecture assumes %d sum inputs while there are %d weights.\n", nSum, Vec_IntSize(vNums)-1 );
        Vec_IntFree( vNums );
        return 0; 
    }
    printf( "Generating threshold function with %d inputs and bit-width %d.\n", Vec_IntSize(vNums)-1, nBits );
    Abc_GenThresh( pFileName, nBits, vNums, nLutSize, pArch );    
    if ( nLutSize == 4 || nLutSize == 6 )
        sprintf(Command, "read %s; strash; if -K %d -am; mfs2 -W 10 -L 10 -M 1000", pFileName, nLutSize );
    else
        sprintf(Command, "read %s", pFileName );
    Cmd_CommandExecute( pAbc, Command );
    Vec_IntFree( vNums );
    return 0;

usage:
    Abc_Print( -2, "usage: gentf [-WK num] [-A str] [-vh] <w1> <w2> ... <wn> <thresh>\n" );
    Abc_Print( -2, "\t         generates threshold function\n" );
    Abc_Print( -2, "\t-W num : the bit-width [default = none]\n" );
    Abc_Print( -2, "\t-K num : the LUT size [default = none]\n" );
    Abc_Print( -2, "\t-A str : the circuit architecture [default = none]\n");
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<nums> : weights and threshold\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGenAT( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_GenAT( char * pFileName, Vec_Int_t * vNums );
    extern void Abc_GenATDual( char * pFileName, Vec_Int_t * vNums );
    int c, fDual = 0, fVerbose = 0;
    char Command[1000], * pFileName = "out.blif";
    Vec_Int_t * vNums = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDual ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind )
        goto usage;
    vNums = Vec_IntAlloc( argc );
    for ( c = globalUtilOptind; c < argc; c++ )
        Vec_IntPush( vNums, atoi(argv[c]) );
    if ( fDual )
        Abc_GenATDual( pFileName, vNums );
    else
        Abc_GenAT( pFileName, vNums );
    sprintf(Command, "read %s", pFileName );
    Cmd_CommandExecute( pAbc, Command );
    Vec_IntFree( vNums );
    return 0;

usage:
    Abc_Print( -2, "usage: genat [-dvh] <n1> <n2> ... <nn>\n" );
    Abc_Print( -2, "\t         generates the adder tree\n" );
    Abc_Print( -2, "\t-d     : toggle building dual tree [default = %s]\n", fDual? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<nums> : input counts by rank\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGenPop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkLutCascadeFromPopcountLuts( int nVars, int nLutSize, int fVerbose, char * pFileName );
    char * pFileName = NULL;
    Abc_Ntk_t * pNtk = NULL;
    int c, nVars = 10, nLutSize = 6, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NKvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    pNtk = Abc_NtkLutCascadeFromPopcountLuts( nVars, nLutSize, fVerbose, pFileName );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Deriving the network has failed.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: genpop [-NK num] [-vh] <file.v>\n" );
    Abc_Print( -2, "\t            generates the adder tree\n" );
    Abc_Print( -2, "\t-N <num>  : the number of support variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-K <num>  : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-v        : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h        : print the command usage\n");
    Abc_Print( -2, "\t-<file.v> : (optional) Verilog file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGenFsm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_GenFsm( char * pFileName, int nIns, int nOuts, int nStates, int nLines, int ProbI, int ProbO );
    int c, nIns, nOuts, nStates, nLines, ProbI, ProbO, fVerbose;
    char * FileName;
    // set defaults
    nIns     =   30;
    nOuts    =    1;
    nStates  =   20;
    nLines   =  100;
    ProbI    =   10;
    ProbO    =  100;
    fVerbose =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IOSLPQvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIns = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIns < 0 )
                goto usage;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            nOuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOuts < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStates = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStates < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLines = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLines < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            ProbI = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( ProbI < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            ProbO = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( ProbO < 0 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }
    if ( nIns < 1 || nStates < 1 || nLines < 1 || ProbI < 1 || ProbO < 1 )
    {
        Abc_Print( -1, "The number of inputs. states, lines, and probablity should be positive integers.\n" );
        goto usage;
    }
    // get the input file name
    FileName = argv[globalUtilOptind];
    Abc_GenFsm( FileName, nIns, nOuts, nStates, nLines, ProbI, ProbO );
    return 0;

usage:
    Abc_Print( -2, "usage: genfsm [-IOSLPQ num] [-vh] <file>\n" );
    Abc_Print( -2, "\t         generates random FSM in KISS format\n" );
    Abc_Print( -2, "\t-I num : the number of input variables [default = %d]\n", nIns );
    Abc_Print( -2, "\t-O num : the number of output variables [default = %d]\n", nOuts );
    Abc_Print( -2, "\t-S num : the number of state variables [default = %d]\n", nStates );
    Abc_Print( -2, "\t-L num : the number of lines (product terms) [default = %d]\n", nLines );
    Abc_Print( -2, "\t-P num : percentage propability of a variable present in the input cube [default = %d]\n", ProbI );
    Abc_Print( -2, "\t-Q num : percentage propability of a variable present in the output cube [default = %d]\n", ProbO );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : output file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestColor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_ColorTest();
    Abc_ColorTest();
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_Gen2CodeTest();
    extern void Dau_NetworkEnumTest();
    //Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nCutMax      =  1;
    int nLeafMax     =  4;
    int nDivMax      =  2;
    int nDecMax      =  3;
    int nNumOnes     =  0;
    int fNewAlgo     =  0;
    int fNewOrder    =  0;
    int fVerbose     =  0;
    int fVeryVerbose =  0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CKDNMaovwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutMax < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLeafMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLeafMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDivMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDivMax < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nDecMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDecMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nNumOnes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNumOnes < 0 )
                goto usage;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'o':
            fNewOrder ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
//    if ( pNtk == NULL )
//    {
//        Abc_Print( -1, "Empty network.\n" );
//        return 1;
//    }
//    if ( Abc_NtkIsStrash(pNtk) )
//    {
//        Abc_Print( -1, "This command works only for logic networks.\n" );
//        return 1;
//    }
//    if ( Abc_NtkLatchNum(pNtk) == 0 )
//    {
//        Abc_Print( -1, "Only works for sequential networks.\n" );
//        return 1;
//    }

//    if ( pNtk )
//    {
//        extern Abc_Ntk_t * Au_ManPerformTest( Abc_Ntk_t * p, int nCutMax, int nLeafMax, int nDivMax, int nDecMax, int fVerbose, int fVeryVerbose );
//        Abc_Ntk_t * pNtkRes = Au_ManPerformTest( pNtk, nCutMax, nLeafMax, nDivMax, nDecMax, fVerbose, fVeryVerbose );
//        if ( pNtkRes == NULL )
//        {
//            Abc_Print( -1, "Command has failed.\n" );
//            return 1;
//        }
//        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
//    }
//    if ( pNtk )
//    {
//        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
//        Saig_ManBmcTerSimTestPo( pAig );
//        Aig_ManStop( pAig );
//    }
//    if ( !Abc_NtkIsTopo(pNtk) )
//    {
//        Abc_Print( -1, "Current network is not in a topological order.\n" );
//        return 1;
//    }
//    if ( pNtk )
//        Abc_NtkMakeLegit( pNtk );
    {
//        extern void Ifd_ManDsdTest();
//        Ifd_ManDsdTest();
    }
//    {
//        extern void Abc_EnumerateCubeStates();
//        extern void Abc_EnumerateCubeStatesZdd();
//        if ( fNewAlgo )
//            Abc_EnumerateCubeStatesZdd();
//        else
//            Abc_EnumerateCubeStates();
//        return 0;
//    }
    {
//        extern void Abc_EnumerateFuncs( int nDecMax, int nDivMax, int fVerbose );
//        Abc_EnumerateFuncs( 4, 7, 0 );
    }
//    if ( fNewAlgo )
//    {
//        extern void Abc_SuppTest( int nOnes, int nVars, int fUseSimple, int fCheck, int fVerbose );
//        Abc_SuppTest( nNumOnes, nDecMax, fNewOrder, 0, fVerbose );
//    }
//    else
//    {
//        extern void Bmc_EcoMiterTest();
//        Bmc_EcoMiterTest();
//    }

    {
//        extern void Nf_ManPrepareLibraryTest();
//        Nf_ManPrepareLibraryTest();
//        return 0;
    }
//    if ( pNtk )
//    {
////        extern Abc_Ntk_t * Abc_NtkBarBufsOnOffTest( Abc_Ntk_t * pNtk );
////        Abc_Ntk_t * pNtkRes = Abc_NtkBarBufsOnOffTest( pNtk );
//        extern Abc_Ntk_t * Abc_NtkPcmTest( Abc_Ntk_t * pNtk, int fNewAlgo, int fVerbose );
////        extern Abc_Ntk_t * Abc_NtkPcmTestAig( Abc_Ntk_t * pNtk, int fVerbose );
//        Abc_Ntk_t * pNtkRes;
////        if ( Abc_NtkIsLogic(pNtk) )
//            pNtkRes = Abc_NtkPcmTest( pNtk, fNewAlgo, fVerbose );
////        else
////            pNtkRes = Abc_NtkPcmTestAig( pNtk, fVerbose );
//        if ( pNtkRes == NULL )
//        {
//            Abc_Print( -1, "Command has failed.\n" );
//            return 1;
//        }
//        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
//    }
//    {
//        extern void Abc_IsopTestNew();
//        Abc_IsopTestNew();
//    }
    {
//        extern void Cba_PrsReadBlifTest();
//        Cba_PrsReadBlifTest();
    }
//    Abc_NtkComputePaths( Abc_FrameReadNtk(pAbc) );
    //Dau_NetworkEnumTest();
    //Extra_SimulationTest( nDivMax, nNumOnes, fNewOrder );
    //Mnist_ExperimentWithScaling( nDecMax );
    //Gyx_ProblemSolveTest();
//    {
//        extern Abc_Ntk_t * Abc_NtkFromArray();
//        Abc_Ntk_t * pNtkRes = Abc_NtkFromArray();
//        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
//    }
    //Gia_ManTestProblem();
    //Abc_ReadPlaTest( "resub2.pla" );
    return 0;
usage:
    Abc_Print( -2, "usage: test [-CKDNM] [-aovwh] <file_name>\n" );
    Abc_Print( -2, "\t         testbench for new procedures\n" );
    Abc_Print( -2, "\t-C num : the max number of cuts [default = %d]\n", nCutMax );
    Abc_Print( -2, "\t-K num : the max number of leaves [default = %d]\n", nLeafMax );
    Abc_Print( -2, "\t-D num : the max number of divisors [default = %d]\n", nDivMax );
    Abc_Print( -2, "\t-N num : the max number of node inputs [default = %d]\n", nDecMax );
    Abc_Print( -2, "\t-M num : the max number of ones in the vector [default = %d]\n", nNumOnes );
    Abc_Print( -2, "\t-a     : toggle using new algorithm [default = %s]\n", fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using new ordering [default = %s]\n", fNewOrder? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSymFun( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Ntk_SymFunGenerate( int nVars, int fVerbose );
    word * pFun = NULL;
    char * pStr,  * pTruth, * pCommand;
    int c, k, nVars = -1, fCounter = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ncvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a file name.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'c':
            fCounter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( fCounter )
    {
        if ( nVars == -1 )
        {
            printf( "The number of variables should be specified on the command line using \"-N <num>\".\n" );
            return 1;
        }
        extern Vec_Ptr_t * Abc_SopGenerateCounters( int nVars );
        Vec_Ptr_t * vSops = Abc_SopGenerateCounters( nVars );
        Abc_Ntk_t * pNtk = Abc_NtkCreateWithNodes( vSops );
        Vec_PtrFreeFree( vSops );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
        Abc_FrameClearVerifStatus( pAbc );
        return 0;
    }
    if ( nVars != -1 )
    {
        if ( nVars < 1 || nVars > 16 )
        {
            printf( "Cannot generate functions for less than 1 and more than %d variables.\n", nVars );
            return 1;
        }
        Ntk_SymFunGenerate( nVars, fVerbose );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Not enough command-line arguments.\n" );
        return 1;
    }
    // make sure the string is composed of N+1 zeros and ones
    pStr = argv[globalUtilOptind];
    nVars = strlen(pStr) - 1;
    for ( k = 0; k <= nVars; k++ )
        if ( pStr[k] != '0' && pStr[k] != '1' )
            break;
    if ( k <= nVars )
    {
        Abc_Print( -1, "The string should be composed of zeros and ones.\n" );
        return 1;
    }
    // generate and print one function
    pFun = Abc_TtSymFunGenerate( pStr, nVars );
    pTruth = ABC_CALLOC( char, nVars > 2 ? (1 << (nVars-2)) + 1 : 2 );
    Extra_PrintHexadecimalString( pTruth, (unsigned *)pFun, nVars );
    ABC_FREE( pFun );
    if ( fVerbose )
    {
        if ( nVars > 6 )
            printf( "Generated truth table of the %d-variable function and set it as the current network.\n", nVars );
        else
            printf( "Generated truth table of the %d-variable function (%s) and set it as the current network\n", nVars, pTruth );
    }
    else if ( nVars <= 8 )
        printf( "%s\n", pTruth );
    // read the truth table to be the current network in ABC
    pCommand = ABC_CALLOC( char, strlen(pTruth) + 100 );
    memcpy( pCommand, "read_truth ", 11 );
    memcpy( pCommand + 11, pTruth, strlen(pTruth) + 1 );
    Cmd_CommandExecute( pAbc, pCommand );
    ABC_FREE( pCommand );
    ABC_FREE( pTruth );
    return 0;

usage:
    Abc_Print( -2, "usage: symfun [-N num] [-cvh] <ones>\n" );
    Abc_Print( -2, "\t           generated a single-output symmetric function\n" );
    Abc_Print( -2, "\t-N <num> : prints truth tables of all N-var symmetric functions [default = not used]\n" );
    Abc_Print( -2, "\t-c       : toggle generating a counter [default = %s]\n", fCounter? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<ones>   : the string of N+1 zeros and ones, where N is the number of variables\n" );
    Abc_Print( -2, "\t           For example, to get 3-input NAND-gate, use \"symfun 1000\".\n" );
    Abc_Print( -2, "\t           To get 5-input majority gate, use \"symfun 000111\".\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCubeEnum( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_EnumerateCubeStates();
    extern void Abc_EnumerateCubeStatesZdd();
    int c, fZddAlgo = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "zvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'z':
            fZddAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( fZddAlgo )
        Abc_EnumerateCubeStatesZdd();
    else
        Abc_EnumerateCubeStates();
    return 0;

usage:
    Abc_Print( -2, "usage: cubeenum [-vh]\n" );
    Abc_Print( -2, "\t         enumerates reachable states of 2x2x2 cube\n" );
    Abc_Print( -2, "\t         (http://en.wikipedia.org/wiki/Pocket_Cube)\n" );
    Abc_Print( -2, "\t-z     : toggle using ZDD-based algorithm [default = %s]\n", fZddAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPathEnum( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_EnumerateFrontierTest( int nSize );
    int c, nSize = 4, fZddAlgo = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSize < 0 )
                goto usage;
            break;
        case 'z':
            fZddAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    Abc_EnumerateFrontierTest( nSize );
    return 0;

usage:
    Abc_Print( -2, "usage: pathenum [-N num] [-vh]\n" );
    Abc_Print( -2, "\t         enumerates self-avoiding paths on the NxN grid\n" );
    Abc_Print( -2, "\t-N num : the size of the grid to consider [default = %d]\n", nSize );
//    Abc_Print( -2, "\t-z     : toggle using ZDD-based algorithm [default = %s]\n", fZddAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFunEnum( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Dtt_EnumerateLf( int nVars, int nNodeMax, int fDelay, int fMulti, int fVerbose, char* pFileName );
    extern void Dau_FunctionEnum( int nInputs, int nVars, int nNodeMax, int fUseTwo, int fReduce, int fVerbose );
    extern Gia_Man_t * Dau_ConstructAigFromFile( char * pFileName );
    int c, nInputs = 4, nVars = 4, nNodeMax = 32, fUseTwo = 0, fReduce = 0, fSimple = 0, fDelay = 0, fMulti = 0, fDump = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SIMtrldmpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nInputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInputs < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeMax < 0 )
                goto usage;
            break;
        case 't':
            fUseTwo ^= 1;
            break;
        case 'r':
            fReduce ^= 1;
            break;
        case 'l':
            fSimple ^= 1;
            break;
        case 'd':
            fDelay ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 'p':
            fDump ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( fSimple || fDelay )
    {
        char Buffer[100];
        if ( nVars < 3 || nVars > 5 )
        {
            Abc_Print( -1, "The number of inputs should be 3 <= I <= 5.\n" );
            goto usage;
        }
        sprintf( Buffer, "Lflib%d.txt", nVars );
        Dtt_EnumerateLf( nVars, nNodeMax, fDelay, fMulti, fVerbose, fDump?Buffer:NULL );
        if ( fDump )
        {
            Gia_Man_t * pTemp;
            pTemp = Dau_ConstructAigFromFile( Buffer );
            Abc_FrameUpdateGia( pAbc, pTemp );
            Gia_DumpAiger( pTemp, "Lflib", nVars, 1 );
        }
    }
    else
    {
        if ( nVars < 2 || nVars > 6 )
        {
            Abc_Print( -1, "The number of inputs should be 2 <= I <= 6.\n" );
            goto usage;
        }
        if ( nInputs < nVars || nInputs > 6 )
        {
            Abc_Print( -1, "The intermediate support size should be I <= S <= 6.\n" );
            goto usage;
        }
        Dau_FunctionEnum( nInputs, nVars, nNodeMax, fUseTwo, fReduce, fVerbose );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: funenum [-SIM num] [-trldmvph]\n" );
    Abc_Print( -2, "\t         enumerates minimum 2-input-gate implementations\n" );
    Abc_Print( -2, "\t-S num : the maximum intermediate support size [default = %d]\n",     nInputs );
    Abc_Print( -2, "\t-I num : the number of inputs of Boolean functions [default = %d]\n", nVars );
    Abc_Print( -2, "\t-M num : the maximum number of 2-input gates [default = %d]\n",       nNodeMax );
    Abc_Print( -2, "\t-t     : toggle adding combination of two gates [default = %s]\n",    fUseTwo?  "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle reducing the last level [default = %s]\n",            fReduce?  "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle generating L(f) rather than C(f) [default = %s]\n",   fSimple?  "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle generating D(f) rather than C(f) [default = %s]\n",   fDelay?   "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle generating multiplicity statistics [default = %s]\n", fMulti?   "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n",                     fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle dumping result library (formula and AIG) [default = %s]\n",fDump?"yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SymFun( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenSymFun( Vec_Wrd_t * vFuns, int nChars, int fVerbose );
    Gia_Man_t * pNew = NULL;
    Vec_Wrd_t * vFuns = NULL;
    int c, nChars = 0, nMaj = 0, nHot = 0, nXor = 0, nWgt = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MHXWvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a file name.\n" );
                goto usage;
            }
            nMaj = atoi(argv[globalUtilOptind++]);
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by a file name.\n" );
                goto usage;
            }
            nHot = atoi(argv[globalUtilOptind++]);
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a file name.\n" );
                goto usage;
            }
            nXor = atoi(argv[globalUtilOptind++]);
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a file name.\n" );
                goto usage;
            }
            nWgt = atoi(argv[globalUtilOptind++]);
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( nMaj ) {
        nChars = nMaj+1;
        vFuns = Vec_WrdAlloc(1);
        Vec_WrdPush( vFuns, Abc_Tt6Mask(nMaj/2+1) << (nMaj/2+1) );        
    }
    else if ( nHot ) {
        nChars = nHot+1;
        vFuns = Vec_WrdAlloc(1);
        Vec_WrdPush( vFuns, 2 );        
    }
    else if ( nXor ) {
        nChars = nXor+1;
        vFuns = Vec_WrdAlloc(1);
        Vec_WrdPush( vFuns, s_Truths6[0] & Abc_Tt6Mask(nChars) );        
    }
    else if ( nWgt ) {
        int nOuts = Abc_Base2Log(nWgt+1);
        nChars = nWgt+1;
        vFuns = Vec_WrdAlloc(nOuts);
        for ( int i = 0; i < nOuts; i++ )
            Vec_WrdPush( vFuns, s_Truths6[i] & Abc_Tt6Mask(nChars) );        
    }
    else {
        if ( argc == globalUtilOptind ) {
            printf( "One or more characteristic strings should be given on the command line.\n" );
            return 0;
        }
        nChars = (int)strlen(argv[globalUtilOptind]);
        for ( c = globalUtilOptind+1; c < argc; c++ )
            if ( nChars != (int)strlen(argv[c]) ) {
                printf( "Char strings have different lengths. Quitting.\n" );
                return 0;            
            }
        vFuns = Vec_WrdAlloc( argc );
        for ( c = globalUtilOptind; c < argc; c++ )
            Vec_WrdPush( vFuns, Abc_TtReadBin64(argv[c]) );
    }
    if ( nChars > 64 ) {
        printf( "Currently can handle functions up to 63 inputs. Quitting.\n" );
        return 0;
    }
    pNew = Gia_ManGenSymFun( vFuns, nChars, fVerbose );
    Abc_FrameUpdateGia( pAbc, pNew );
    Vec_WrdFree( vFuns );
    return 0;

usage:
    Abc_Print( -2, "usage: &symfun [-MHXW num] [-vh] <str0> <str1> ... <str(N-1)>\n" );
    Abc_Print( -2, "\t           derives AIG of a multi-output symmetric function\n" );
    Abc_Print( -2, "\t-M <num> : generate the majority gate with the given input count [default = unused]\n" );
    Abc_Print( -2, "\t-H <num> : generate the 1-hot condition with the given input count [default = unused]\n" );
    Abc_Print( -2, "\t-X <num> : generate the xor-gate with the given input count [default = unused]\n" );
    Abc_Print( -2, "\t-W <num> : generate the weight(W) function with the given input count [default = unused]\n" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<str0> <str1> ... <str(N-1)> : char strings in binary notation LSB first\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Mesh( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Bmc_MeshTest( Gia_Man_t * p, int X, int Y, int T, int fVerbose );
    extern void Bmc_MeshTest2( Gia_Man_t * p, int X, int Y, int T, int fVerbose );
    int X =  4;
    int Y =  4;
    int T =  3;
    int fUseSatoko = 1;
    int c, fVerbose = 1;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "XYTsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            X = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( X < 3 )
                goto usage;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by an integer.\n" );
                goto usage;
            }
            Y = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Y < 3 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            T = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( T < 2 )
                goto usage;
            break;
        case 's':
            fUseSatoko ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Mesh(): There is no design.\n" );
        return 1;
    }
    if ( Gia_ManCoNum(pAbc->pGia) != 1 )
    {
        Abc_Print( -1, "Currently this command expects AIG with one output.\n" );
        return 1;
    }
    if ( Gia_ManCiNum(pAbc->pGia) > 20 )
    {
        Abc_Print( -1, "Currently this command expects AIG with no more than 20 nodes.\n" );
        return 1;
    }
    if ( Gia_ManLevelNum(pAbc->pGia) > T )
    {
        Abc_Print( -1, "The depth of the AIG (%d) cannot be larger than the latency (%d).\n", Gia_ManLevelNum(pAbc->pGia), T );
        return 1;
    }
    if ( fUseSatoko )
        Bmc_MeshTest( pAbc->pGia, X, Y, T, fVerbose );
    else
        Bmc_MeshTest2( pAbc->pGia, X, Y, T, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &mesh [-XYT num] [-sh]\n" );
    Abc_Print( -2, "\t         creates a mesh architecture for the given AIG\n" );
    Abc_Print( -2, "\t-X num : horizontal size of the mesh (X >= 3) [default = %d]\n", X );
    Abc_Print( -2, "\t-Y num : vertical size of the mesh (Y >= 3) [default = %d]\n", Y );
    Abc_Print( -2, "\t-T num : the latency of the mesh (T >= 2) [default = %d]\n", T );
    Abc_Print( -2, "\t-s     : toggle using new SAT solver Satoko [default = %s]\n", fUseSatoko? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenLutCas( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenLutCas( Gia_Man_t * p, char * pPermStr, int nVars, int nLuts, int LutSize, int Seed, int fVerbose );
    int nVars    =  0;
    int nLuts    =  2;
    int LutSize  =  6;
    int Seed     =  0;
    int fVerbose =  0;
    int c;
    char * pPermStr = NULL;
    Gia_Man_t * pTemp;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMKSPvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nLuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLuts < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            LutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LutSize < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Seed < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a string.\n" );
                goto usage;
            }
            pPermStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL && nVars == 0 ) 
    {
        Abc_Print( -1, "The number of inputs (%d) should be specified on the command line.\n", nVars );
        return 1;        
    }
    if ( pAbc->pGia )
        nVars = Gia_ManCiNum(pAbc->pGia);
    if ( pPermStr && (nLuts * LutSize != (int)strlen(pPermStr)) )
    {
        Abc_Print( -1, "Permutation \"%s\" has %d symbols instead of expected %d = %d * %d symbols (LutSize * nLuts).\n", 
            pPermStr, (int)strlen(pPermStr), LutSize * nLuts, LutSize, nLuts );
        return 1;
    }
    if ( nVars <= LutSize )
    {
        Abc_Print( -1, "The number of inputs (%d) should be more than LUT size (%d).\n", nVars, LutSize );
        return 1;
    }
    if ( nVars > 100 )
    {
        Abc_Print( -1, "The number of inputs (%d) should be less than 100.\n", nVars );
        return 1;
    }
    if ( nLuts < 2 || nLuts > 100  )
    {
        Abc_Print( -1, "The LUT count (%d) should be morein the range [2;100].\n", nLuts );
        return 1;
    }
    if ( LutSize < 2 || LutSize > 12 )
    {
        Abc_Print( -1, "The LUT size (%d) should be in the range [2;12].\n", LutSize );
        return 1;
    }
    if ( nVars > (nLuts-1)*(LutSize-1) + LutSize )
    {
        Abc_Print( -1, "Function with %d variables is too large for a cascade composed of %d connected %d-LUTs.\n", nVars, nLuts, LutSize );
        return 1;
    }
    pTemp = Gia_ManGenLutCas( pAbc->pGia, pPermStr, nVars, nLuts, LutSize, Seed, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &genlutcas[-NMKS num] [-P str] [-vh]\n" );
    Abc_Print( -2, "\t         generates a miter for synthesizing the LUT cascade\n" );
    Abc_Print( -2, "\t-N num : the number of primary inputs [default = %d]\n", nVars );
    Abc_Print( -2, "\t-M num : the number of LUTs [default = %d]\n", nLuts );
    Abc_Print( -2, "\t-K num : the LUT size [default = %d]\n", LutSize );
    Abc_Print( -2, "\t-S num : the random seed [default = %d]\n", Seed );
    Abc_Print( -2, "\t-P str : variable permutation (for example, \"abcd_aef\" for S44) [default = %s]\n", pPermStr ? pPermStr : "unused" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Gen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Extra_CommandGen( int Algo, int LutSize, int nLuts, int nLevels, int Limit, int nBestTries, int Multi, int fXor, int fVerbose );
    Gia_Man_t * pTemp = NULL;
    int Algo        =   0;
    int LutSize     =   6;
    int nLuts       = 256;
    int nLevels     =   8;
    int Limit       =   0;
    int nBestTries  =   1;
    int Multi       =   0;
    int fXor        =   1;
    int c, fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "AKNDLBMxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            Algo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Algo < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            LutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LutSize < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLuts < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            Limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Limit < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBestTries = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBestTries < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            Multi = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Multi < 0 )
                goto usage;
            break;
        case 'x':
            fXor ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pTemp = Extra_CommandGen( Algo, LutSize, nLuts, nLevels, Limit, nBestTries, Multi, fXor, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &gen [-AKNDLBMxvh]\n" );
    Abc_Print( -2, "\t          generates network\n" );
    Abc_Print( -2, "\t-A num  : the generation algorithm [default = %d]\n",                 Algo );
    Abc_Print( -2, "\t-K num  : the number of LUT inputs [default = %d]\n",                 LutSize );
    Abc_Print( -2, "\t-N num  : the number of LUTs on one level [default = %d]\n",          nLuts );
    Abc_Print( -2, "\t-D num  : the number of LUT levels [default = %d]\n",                 nLevels );
    Abc_Print( -2, "\t-L num  : limit below which we randomize [default = %d]\n",           Limit );
    Abc_Print( -2, "\t-B num  : select best fanins among this many tries [default = %d]\n", nBestTries );
    Abc_Print( -2, "\t-M num  : the multiplier type (1=array, 2=booth) [default = %d]\n",   Multi );
    Abc_Print( -2, "\t-x      : toggle using XOR gates [default = %s]\n",                   fXor? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n",      fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenHie( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_GenSandwich( char ** pFNames, int nFNames, char * pFileName );
    char * pFileName = (char *)"sandwich.v";
    int c, fVerbose = 0;
    char ** pArgvNew;
    int     nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileName = argv[globalUtilOptind++];
            break;            
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;    
    if ( nArgcNew < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenHie(): At least one AIG file should be given on the command line.\n" );
        return 0;
    }        
    Gia_GenSandwich( pArgvNew, nArgcNew, pFileName );
    return 0;
usage:
    Abc_Print( -2, "usage: &gen_hie [-F <file>] [-vh] <file[1]> <file[2]> ...  <file[N]>\n" );
    Abc_Print( -2, "\t            generates a hierarchical design in Verilog\n" );
    Abc_Print( -2, "\t-F <file> : the output file name (optional) [default = \"sandwich.v\"]\n" );
    Abc_Print( -2, "\t-v        : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h        : print the command usage\n");
    Abc_Print( -2, "\t<files>   : the AIG files for the instance modules\n");    
    Abc_Print( -2, "\t            (the PO count of <file[i]> should not be less than the PI count of <file[i+1]>)\n");    
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenRel( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManGenRel( Gia_Man_t * pGia, Vec_Int_t * vInsOuts, int nIns, char * pFileName, int fVerbose );
    Vec_Int_t * vInsOuts = NULL; char * pIns = NULL, * pOuts = NULL;
    int c, nIns = -1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IOvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pIns = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            pOuts = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenRel(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind+1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenRel(): The output file name should be given as the last entry on the command line.\n" );
        return 0;
    }
    if ( pIns == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenRel(): A comma-separated list of window input node IDs should be given as \"-I list\" on the command line.\n" );
        return 0;
    }
    if ( pOuts == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenRel(): A comma-separated list of window output node IDs should be given as \"-O list\" on the command line.\n" );
        return 0;
    }
    vInsOuts = Vec_IntAlloc( 16 );
    Vec_IntPush( vInsOuts, atoi(pIns) );
    for ( c = 0; pIns[c]; c++ )
        if ( pIns[c] == ',' )
            Vec_IntPush( vInsOuts, atoi(pIns+c+1) );
    nIns = Vec_IntSize(vInsOuts);
    Vec_IntPush( vInsOuts, atoi(pOuts) );
    for ( c = 0; pOuts[c]; c++ )
        if ( pOuts[c] == ',' )
            Vec_IntPush( vInsOuts, atoi(pOuts+c+1) );
    if ( fVerbose ) {
        printf( "Deriving relation for %d inputs and %d outputs: ", nIns, Vec_IntSize(vInsOuts)-nIns );
        Vec_IntPrint( vInsOuts );
    }
    Gia_ManGenRel( pAbc->pGia, vInsOuts, nIns, argv[globalUtilOptind], fVerbose );
    Vec_IntFree( vInsOuts );
    return 0;

usage:
    Abc_Print( -2, "usage: &genrel [-I n1,n2,...nN] [-O m1,m2,...,mM] [-vh] <filename>\n" );
    Abc_Print( -2, "\t          generates Boolean relation for the given logic window\n" );
    Abc_Print( -2, "\t-I list : comma-separated list of window inputs [default = undefined]\n" );
    Abc_Print( -2, "\t-O list : comma-separated list of window outputs [default = undefined]\n" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<file>  : the output file name (PLA format extended to represented Boolean relations)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenMux( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenMux( int nIns, char * pNums );
    Gia_Man_t * pTemp = NULL;
    int c, nIns = 0, fVerbose = 0;
    char * pNums = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nIns = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIns < 0 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind && nIns > 0 ) 
    {
        extern char * Wlc_NtkMuxTreeString( int nIns );
        if ( nIns <= 16 )
            pNums = Wlc_NtkMuxTreeString( nIns );
        else
        {
            Abc_Print( -1, "Abc_CommandAbc9GenMux(): The number of controls should not be in the range: 2 <= n <= 16.\n" );
            return 0;            
        }
    }
    else if ( argc == globalUtilOptind+1 ) 
    {
        int nIns2 = 0;
        pNums = argv[globalUtilOptind];
        for ( c = 0; pNums[c]; c++ )
            nIns2 += (int)(pNums[c] - '0');
        if ( nIns > 0 && nIns2 > 0 && nIns != nIns2 ) 
        {
            Abc_Print( -1, "Abc_CommandAbc9GenMux(): The number of inputs does not match.\n" );
            return 0;
        }
        nIns = nIns2;
    }
    else
    {
        Abc_Print( -1, "Abc_CommandAbc9GenMux(): The number of controls or the control input groups should be given on the command line.\n" );
        return 0;
    }
    pTemp = Gia_ManGenMux( nIns, pNums );
    Abc_FrameUpdateGia( pAbc, pTemp );    
    Abc_Print( 1, "Generated a %d:1 MUX with the following groups: %s\n", 1<<nIns, pNums );
    return 0;

usage:
    Abc_Print( -2, "usage: &genmux [-K <num>] [-vh] <string>\n" );
    Abc_Print( -2, "\t         generates the multiplexer\n" );
    Abc_Print( -2, "\t-K num : the number of control inputs [default = undefined]\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tstring : the sizes of control input groups\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Test( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPrintArray( Gia_Man_t * p );
    extern Gia_Man_t * Gia_ManPerformNewResub( Gia_Man_t * p, int nWinCount, int nCutSize, int nProcs, int fVerbose );
    extern void Gia_RsbEnumerateWindows( Gia_Man_t * p, int nInputsMax, int nLevelsMax );
    extern int Gia_ManSumTotalOfSupportSizes( Gia_Man_t * p );
    extern void Abc_Tt6MinTest2( Gia_Man_t * p );
    int c, fVerbose = 0;
    int nFrames = 5;
    int fSwitch = 0;
    int nWords = 1000;
    int nProcs = 2;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WPFsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProcs < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 )
                goto usage;
            break;
        case 's':
            fSwitch ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
//    Gia_Obj_t * pObj; int i;
//    Gia_ManCreateRefs(pAbc->pGia);
//    Gia_ManForEachAnd( pAbc->pGia, pObj, i )
//        if ( !Gia_ObjIsLut(pAbc->pGia, i) && Gia_ObjRefNum(pAbc->pGia, pObj) > 1 )
//            printf( "%d ", Gia_ObjRefNum(pAbc->pGia, pObj) );
//    printf( "\n" );
//    return 0;
//    
//    extern void cadical_solver_test();
//    cadical_solver_test();
//    return 0;
//    extern void kissat_solver_test();
//    kissat_solver_test();
//    return 0;    
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Test(): There is no AIG.\n" );
        return 1;
    }
    if ( argc == globalUtilOptind + 1 )
    {
        extern void Gia_ManUpdateCoPhase( Gia_Man_t * pNew, Gia_Man_t * pOld );
        Gia_Man_t * pTemp = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
        Gia_ManUpdateCoPhase( pAbc->pGia, pTemp );
        Gia_ManStop( pTemp );
        return 0;
    }
    //Abc_FrameUpdateGia( pAbc, pNew );
//    printf( "AIG in \"%s\" has the sum of output support sizes equal to %d.\n", pAbc->pGia->pSpec, Gia_ManSumTotalOfSupportSizes(pAbc->pGia) );
    return 0;
usage:
    Abc_Print( -2, "usage: &test [-FW num] [-svh]\n" );
    Abc_Print( -2, "\t        testing various procedures\n" );
    Abc_Print( -2, "\t-F num: the number of timeframes [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-W num: the number of machine words [default = %d]\n", nWords );
    Abc_Print( -2, "\t-s    : toggle enable (yes) vs. disable (no) [default = %s]\n", fSwitch? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
