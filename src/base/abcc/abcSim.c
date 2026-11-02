/**CFile****************************************************************

  FileName    [abcSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Simulation and counterexamples.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "opt/sim/sim.h"
#include "aig/saig/saig.h"
#include "sat/bmc/bmc.h"
#include "bool/kit/kit.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandFaultClasses           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAigSim                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandXsim                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSim                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSim3                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestCex                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCexSave                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCexLoad                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCexCut                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCexMerge               ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandCexMin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sim                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sim2               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sim3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MLGen              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MLTest             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Iwls21Test         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadSim            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9WriteSim           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PrintSim           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenSim             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resim              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AdvGenSim          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LNetSim            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LNetEval           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Era                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9CexInfo            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9FFTest             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Inse               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Maxi               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PoXsim             ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandAbc9CexCut             ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandAbc9CexMerge           ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandAbc9CexMin             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cfs                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenCex             ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
extern void Extra_BitMatrixTransposeP( Vec_Wrd_t * vSimsIn, int nWordsIn, Vec_Wrd_t * vSimsOut, int nWordsOut );

/**Function*************************************************************

  Synopsis    [Registers simulation and counterexamples commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitSim( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "faultclasses",  Abc_CommandFaultClasses,     0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "aigsim",        Abc_CommandAigSim,           0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "xsim",          Abc_CommandXsim,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "sim",           Abc_CommandSim,              0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "sim3",          Abc_CommandSim3,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "testcex",       Abc_CommandTestCex,          0 );
    Cmd_CommandAdd( pAbc, "Verification", "cexsave",       Abc_CommandCexSave,          0 );
    Cmd_CommandAdd( pAbc, "Verification", "cexload",       Abc_CommandCexLoad,          0 );
    Cmd_CommandAdd( pAbc, "Verification", "cexcut",        Abc_CommandCexCut,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "cexmerge",      Abc_CommandCexMerge,         0 );
//    Cmd_CommandAdd( pAbc, "Verification", "cexmin",        Abc_CommandCexMin,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim",          Abc_CommandAbc9Sim,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim2",         Abc_CommandAbc9Sim2,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim3",         Abc_CommandAbc9Sim3,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mlgen",        Abc_CommandAbc9MLGen,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mltest",       Abc_CommandAbc9MLTest,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&iwls21test",   Abc_CommandAbc9Iwls21Test,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim_read",     Abc_CommandAbc9ReadSim,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim_write",    Abc_CommandAbc9WriteSim,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim_print",    Abc_CommandAbc9PrintSim,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim_gen",      Abc_CommandAbc9GenSim,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resim",        Abc_CommandAbc9Resim,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&adv_sim_gen",      Abc_CommandAbc9AdvGenSim,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lnetsim",      Abc_CommandAbc9LNetSim,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lneteval",     Abc_CommandAbc9LNetEval,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&era",          Abc_CommandAbc9Era,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cexinfo",      Abc_CommandAbc9CexInfo,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&fftest",       Abc_CommandAbc9FFTest,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&inse",         Abc_CommandAbc9Inse,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&maxi",         Abc_CommandAbc9Maxi,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&poxsim",       Abc_CommandAbc9PoXsim,       0 );
//    Cmd_CommandAdd( pAbc, "ABC9",         "&cexcut",       Abc_CommandAbc9CexCut,       0 );
//    Cmd_CommandAdd( pAbc, "ABC9",         "&cexmerge",     Abc_CommandAbc9CexMerge,     0 );
//    Cmd_CommandAdd( pAbc, "ABC9",         "&cexmin",       Abc_CommandAbc9CexMin,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cfs",          Abc_CommandAbc9Cfs,                    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gencex",       Abc_CommandAbc9GenCex,                 0 );    
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
int Abc_CommandFaultClasses( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkDetectClassesTest( Abc_Ntk_t * pNtk, int fSeq, int fVerbose, int fVeryVerbose );
    extern void Abc_NtkGenFaultList( Abc_Ntk_t * pNtk, char * pFileName, int fStuckAt );
    Abc_Ntk_t * pNtk;
    int c, fGen = 0, fStuckAt = 0, fSeq = 0, fVerbose = 0, fVeryVerbose = 0;
    pNtk = Abc_FrameReadNtk(pAbc);
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "gcsvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'g':
            fGen ^= 1;
            break;
        case 'c':
            fStuckAt ^= 1;
            break;
        case 's':
            fSeq ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only applicable to a logic network.\n" );
        return 1;
    }
    if ( fGen )
    {
        char * pFileName = Extra_FileNameGenericAppend(Abc_NtkSpec(pNtk), "_faults.txt");
        Abc_NtkGenFaultList( pNtk, pFileName, fStuckAt );
    }
    else
        Abc_NtkDetectClassesTest( pNtk, fSeq, fVerbose, fVeryVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: faultclasses [-gcsvwh]\n" );
    Abc_Print( -2, "\t           computes equivalence classes of faults in the given mapped netlist;\n" );
    Abc_Print( -2, "\t           the fault list with faults in the format: <fault_id> <node_name> <fault_name>\n" );
    Abc_Print( -2, "\t           should be read by command \"read_fins\" before calling this command\n" );
    Abc_Print( -2, "\t-g       : toggle generating a fault list for the current mapped network [default = %s]\n", fGen? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle using only stuck-at faults in the generated fault list [default = %s]\n", fStuckAt? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle detecting sequential equivalence classes [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout during computation [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing of resulting fault equivalence classes [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAigSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int SimulateAigTop( char *fname1, char *fname2, char * mask, int verbose );
    char * pMask = NULL;
    char ** pArgvNew = NULL;
    int nArgcNew = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a string.\n" );
                goto usage;
            }
            pMask = argv[globalUtilOptind];
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
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 2 ) {
        Abc_Print( -1, "Expecting two files names on the command line.\n" );
        return 1;
    }
    SimulateAigTop( pArgvNew[0], pArgvNew[1], pMask, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: aigsim -M <str> [-vh] <file1> <file2>\n" );
    Abc_Print( -2, "\t           combinational AIG simulation\n" );
    Abc_Print( -2, "\t-M <str> : mask to select inputs for simulation [default = unused]\n" );
    Abc_Print( -2, "\t-v       : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file1>  : the first file to simulate\n");
    Abc_Print( -2, "\t<file2>  : the second file to simulate\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandXsim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int fXInputs;
    int fXState;
    int fVerbose;
    extern void Abc_NtkXValueSimulate( Abc_Ntk_t * pNtk, int nFrames, int fXInputs, int fXState, int fVerbose );
    // set defaults
    nFrames    = 10;
    fXInputs   =  0;
    fXState    =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fisvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'i':
            fXInputs ^= 1;
            break;
        case 's':
            fXState ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    Abc_NtkXValueSimulate( pNtk, nFrames, fXInputs, fXState, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: xsim [-F num] [-isvh]\n" );
    Abc_Print( -2, "\t         performs X-valued simulation of the AIG\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i     : toggle X-valued representation of inputs [default = %s]\n", fXInputs? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle X-valued representation of state [default = %s]\n", fXState? "yes": "no" );
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
int Abc_CommandSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fNew;
    int fComb;
    int nFrames;
    int nWords;
    int TimeOut;
    int fMiter;
    int fVerbose;
    char * pFileSim;
    char * pLogFileName = NULL;
    extern int Abc_NtkDarSeqSim( Abc_Ntk_t * pNtk, int nFrames, int nWords, int TimeOut, int fNew, int fMiter, int fVerbose, char * pFileSim );
    // set defaults
    fNew       =  0;
    fComb      =  0;
    nFrames    = 32;
    nWords     =  8;
    TimeOut    = 30;
    fMiter     =  1;
    fVerbose   =  0;
    pFileSim   = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWTALnmvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileSim = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'n':
            fNew ^= 1;
            break;
        case 'm':
            fMiter ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    if ( pFileSim != NULL && Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "Currently simulation with user-specified patterns works only for comb miters.\n" );
        return 1;
    }
    ABC_FREE( pNtk->pSeqModel );
    pAbc->Status = Abc_NtkDarSeqSim( pNtk, nFrames, nWords, TimeOut, fNew, fMiter, fVerbose, pFileSim );
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "sim" );
    return 0;

usage:
    Abc_Print( -2, "usage: sim [-FWT num] [-AL file] [-nmvh]\n" );
    Abc_Print( -2, "\t          performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num  : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-W num  : the number of words to simulate [default = %d]\n", nWords );
    Abc_Print( -2, "\t-T num  : approximate runtime limit in seconds [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-A file : text file name with user's patterns [default = random simulation]\n" );
    Abc_Print( -2, "\t          (patterns are listed, one per line, as sequences of 0s and 1s)\n" );
    Abc_Print( -2, "\t-L file : the log file name [default = %s]\n",  pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-n      : toggle new vs. old implementation [default = %s]\n", fNew? "new": "old" );
    Abc_Print( -2, "\t-m      : toggle miter vs. any circuit [default = %s]\n", fMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSim3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkDarSeqSim3( Abc_Ntk_t * pNtk, Ssw_RarPars_t * pPars );
    Ssw_RarPars_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    Vec_Ptr_t * vSeqModelVec;
    char * pLogFileName = NULL;
    int c;
    Ssw_RarSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRSNTGLadivzh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBinSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBinSize < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRestart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRestart < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRandSeed < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOut < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOutGap = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOutGap < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'a':
            pPars->fSolveAll ^= 1;
            break;
        case 'd':
            pPars->fDropSatOuts ^= 1;
            break;
        case 'i':
            pPars->fSetLastState ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'z':
            pPars->fNotVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Only works for sequential networks.\n" );
        return 1;
    }
    ABC_FREE( pNtk->pSeqModel );
    pAbc->Status = Abc_NtkDarSeqSim3( pNtk, pPars );
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    vSeqModelVec = pNtk->vSeqModelVec;  pNtk->vSeqModelVec = NULL;
    if ( pPars->fSetLastState && pAbc->pNtkCur->pData )
    {
        Abc_Obj_t * pObj;
        Vec_Int_t * vInit = (Vec_Int_t *)pAbc->pNtkCur->pData;
        pAbc->pNtkCur->pData = NULL;
        Abc_NtkForEachLatch( pAbc->pNtkCur, pObj, c )
            if ( Vec_IntEntry(vInit, c) )
                Abc_LatchSetInit1( pObj );
        Vec_IntFree( vInit );
        pNtkRes = Abc_NtkRestrashZero( pAbc->pNtkCur, 0 );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Removing SAT outputs has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        pNtk = Abc_FrameReadNtk(pAbc);
    }
    if ( pPars->fSolveAll && pPars->fDropSatOuts )
    {
        if ( vSeqModelVec == NULL )
            Abc_Print( 1,"The array of counter-examples is not available.\n" );
        else if ( Vec_PtrSize(vSeqModelVec) != Abc_NtkPoNum(pNtk) )
            Abc_Print( 1,"The array size does not match the number of outputs.\n" );
        else
        {
            extern void Abc_NtkDropSatOutputs( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCexes, int fVerbose );
            Abc_NtkDropSatOutputs( pNtk, vSeqModelVec, pPars->fVerbose );
            pNtkRes = Abc_NtkDarLatchSweep( pNtk, 1, 1, 1, 0, -1, -1, 0, 0 );
            if ( pNtkRes == NULL )
            {
                Abc_Print( -1, "Removing SAT outputs has failed.\n" );
                return 1;
            }
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        }
    }
    if ( vSeqModelVec )
    {
        Abc_FrameReplaceCexVec( pAbc, &vSeqModelVec );
        pAbc->nFrames = -1;
    }
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "sim3" );
    return 0;

usage:
    Abc_Print( -2, "usage: sim3 [-FWBRSNTG num] [-L file] [-advzh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n",                         pPars->nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",                          pPars->nWords );
    Abc_Print( -2, "\t-B num : the number of flops in one bin [default = %d]\n",                           pPars->nBinSize );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n",                          pPars->nRounds );
    Abc_Print( -2, "\t-S num : the number of rounds before a restart [default = %d]\n",                    pPars->nRestart );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n",                    pPars->nRandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n",                     pPars->TimeOut );
    Abc_Print( -2, "\t-G num : approximate runtime gap in seconds since the last CEX [default = %d]\n",    pPars->TimeOutGap );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n",                                          pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-a     : toggle solving all outputs (do not stop when one is SAT) [default = %s]\n", pPars->fSolveAll?    "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dropping (replacing by 0) SAT outputs [default = %s]\n",             pPars->fDropSatOuts? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle changing init state to a last rare state [default = %s]\n",          pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",                      pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle suppressing report about solved outputs [default = %s]\n",           pPars->fNotVerbose?  "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestCex( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int c;
    int nOutputs = 0;
    int fCheckAnd = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Oah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            nOutputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOutputs < 0 )
                goto usage;
            break;
        case 'a':
            fCheckAnd ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }

    if ( !fCheckAnd )
    {
        // check the main AIG
        pNtk = Abc_FrameReadNtk(pAbc);
        if ( pNtk == NULL )
            Abc_Print( 1, "Main AIG: There is no current network.\n");
        else if ( !Abc_NtkIsStrash(pNtk) )
            Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        else if ( Abc_NtkPiNum(pNtk) != pAbc->pCex->nPis )
            Abc_Print( 1, "Main AIG: The number of PIs (%d) is different from cex (%d).\n", Abc_NtkPiNum(pNtk), pAbc->pCex->nPis );
        else
        {
            extern int Abc_NtkVerifyCex( Abc_Ntk_t * pNtk, Abc_Cex_t * p );
            int iPoOld = pAbc->pCex->iPo;
            pAbc->pCex->iPo = Abc_NtkVerifyCex( pNtk, pAbc->pCex );
            if ( pAbc->pCex->iPo == -1 )
                Abc_Print( 1, "Main AIG: The cex does not fail any outputs.\n" );
            else if ( iPoOld != pAbc->pCex->iPo )
                Abc_Print( 1, "Main AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
            else
                Abc_Print( 1, "Main AIG: The cex is correct.\n" );
        }
    }
    else
    {
        // check the AND AIG
        if ( pAbc->pGia == NULL )
            Abc_Print( 1, "And  AIG: There is no current network.\n");
        else if ( Gia_ManPiNum(pAbc->pGia) != pAbc->pCex->nPis )
            Abc_Print( 1, "And  AIG: The number of PIs (%d) is different from cex (%d).\n", Gia_ManPiNum(pAbc->pGia), pAbc->pCex->nPis );
        else
        {
            int iPoOld = pAbc->pCex->iPo;
            pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pAbc->pGia, pAbc->pCex, nOutputs );
            if ( pAbc->pCex->iPo == -1 )
                Abc_Print( 1, "And  AIG: The cex does not fail any outputs.\n" );
            else if ( iPoOld != pAbc->pCex->iPo )
                Abc_Print( 1, "And  AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
            else
                Abc_Print( 1, "And  AIG: The cex is correct.\n" );
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: testcex [-O num] [-ah]\n" );
    Abc_Print( -2, "\t         tests the current cex against the current AIG or the &-AIG\n" );
    Abc_Print( -2, "\t-O num : the number of real POs in the PO list [default = %d]\n", nOutputs );
    Abc_Print( -2, "\t-a     : toggle checking the current AIG or the &-AIG [default = %s]\n", fCheckAnd ? "&-AIG": "current AIG" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCexSave( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Current CEX is not available..\n" );
        return 1;
    }
    ABC_FREE( pAbc->pCex2 );
    pAbc->pCex2 = Abc_CexDup( pAbc->pCex, -1 );
    return 0;

usage:
    Abc_Print( -2, "usage: cexsave [-h]\n" );
    Abc_Print( -2, "\t        saves the current CEX into the internal storage\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCexLoad( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pCex2 == NULL )
    {
        Abc_Print( -1, "Saved CEX is not available.\n" );
        return 1;
    }
    ABC_FREE( pAbc->pCex );
    pAbc->pCex = Abc_CexDup( pAbc->pCex2, -1 );
    // update status
    pAbc->nFrames = pAbc->pCex2->iFrame;
    pAbc->Status = 0;
    return 0;

usage:
    Abc_Print( -2, "usage: cexload [-h]\n" );
    Abc_Print( -2, "\t        loads the current CEX from the internal storage\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCexCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkNew;
    int c, iFrStart = 0;
    int iFrStop     = ABC_INFINITY;
    int fCombOnly   = 0;
    int fUseOne     = 0;
    int fAllFrames  = 0;
    int fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FGcnmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStop = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStop < 0 )
                goto usage;
            break;
        case 'c':
            fCombOnly ^= 1;
            break;
        case 'n':
            fUseOne ^= 1;
            break;
        case 'm':
            fAllFrames ^= 1;
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

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( 1, "There is no AIG in the &-space.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pAbc->pNtkCur) )
    {
        Abc_Print( 1, "Current network is not an AIG.\n");
        return 0;
    }
    if ( iFrStop == ABC_INFINITY )
        iFrStop = pAbc->pCex->iFrame;

    {
        Aig_Man_t * pAig = Abc_NtkToDar( pAbc->pNtkCur, 0, 1 );
        Aig_Man_t * pAigNew = Bmc_AigTargetStates( pAig, pAbc->pCex, iFrStart, iFrStop, fCombOnly, fUseOne, fAllFrames, fVerbose );
        Aig_ManStop( pAig );
        if ( pAigNew == NULL )
        {
            Abc_Print( 1, "Command has failed.\n");
            return 0;
        }
        pNtkNew = Abc_NtkFromAigPhase( pAigNew );
        pNtkNew->pName = Extra_UtilStrsav( pAbc->pNtkCur->pName );
        Aig_ManStop( pAigNew );
        // update the network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    }
//    pGiaNew = Bmc_GiaTargetStates( pAbc->pGia, pAbc->pCex, iFrStart, iFrStop, fCombOnly, fUseOne, fVerbose );
//    if ( pGiaNew == NULL )
//    {
//        Abc_Print( 1, "Command has failed.\n");
//        return 0;
//    }
//    Abc_FrameUpdateGia( pAbc, pGiaNew );
    return 0;

usage:
    Abc_Print( -2, "usage: cexcut [-FG num] [-cnmvh]\n" );
    Abc_Print( -2, "\t         creates logic for bad states using the current CEX\n" );
    Abc_Print( -2, "\t-F num : 0-based number of the starting frame [default = %d]\n", iFrStart );
    Abc_Print( -2, "\t-G num : 0-based number of the ending frame [default = %d]\n",   iFrStop );
    Abc_Print( -2, "\t-c     : toggle outputting unate combinational circuit [default = %s]\n",  fCombOnly? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle generating only one bad state [default = %s]\n", fUseOne? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle generating bad states for all frames after G [default = %s]\n", fAllFrames? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCexMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Cex_t * pCexNew;
    int c;
    int iFrStart = 0;
    int iFrStop  = ABC_INFINITY;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FGvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStop = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStop < 0 )
                goto usage;
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

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }
    if ( pAbc->pCex2 == NULL )
    {
        Abc_Print( 1, "There is no saved cex.\n");
        return 0;
    }
    if ( iFrStop - iFrStart + pAbc->pCex->iPo < pAbc->pCex->iFrame )
    {
        Abc_Print( 1, "Current CEX does not allow to shorten the saved CEX.\n");
        return 0;
    }
    pCexNew = Abc_CexMerge( pAbc->pCex2, pAbc->pCex, iFrStart, iFrStop );
    if ( pCexNew == NULL )
    {
        Abc_Print( 1, "Merging CEXes has failed.\n");
        return 0;
    }
    // replace the saved CEX
    ABC_FREE( pAbc->pCex2 );
    pAbc->pCex2 = pCexNew;
    return 0;

usage:
    Abc_Print( -2, "usage: cexmerge [-FG num] [-vh]\n" );
    Abc_Print( -2, "\t         merges the current CEX into the saved one\n" );
    Abc_Print( -2, "\t         and sets the resulting CEX as the saved one\n" );
    Abc_Print( -2, "\t-F num : 0-based number of the starting frame [default = %d]\n", iFrStart );
    Abc_Print( -2, "\t-G num : 0-based number of the ending frame [default = %d]\n",   iFrStop );
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
int Abc_CommandCexMin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    Abc_Cex_t * vCexNew = NULL;
    int c;
    int nConfLimit = 1000;
    int nRounds    =    1;
    int fVerbose   =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 )
                goto usage;
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

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
        Abc_Print( 1, "Main AIG: There is no current network.\n");
    else if ( !Abc_NtkIsStrash(pNtk) )
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
    else if ( Abc_NtkPiNum(pNtk) != pAbc->pCex->nPis )
        Abc_Print( 1, "Main AIG: The number of PIs (%d) is different from cex (%d).\n", Abc_NtkPiNum(pNtk), pAbc->pCex->nPis );
//      else if ( Abc_NtkLatchNum(pNtk) != pAbc->pCex->nRegs )
//          Abc_Print( 1, "Main AIG: The number of registers (%d) is different from cex (%d).\n", Abc_NtkLatchNum(pNtk), pAbc->pCex->nRegs );
//      else if ( Abc_NtkPoNum(pNtk) <= pAbc->pCex->iPo )
//          Abc_Print( 1, "Main AIG: The number of POs (%d) is less than the PO index in cex (%d).\n", Abc_NtkPoNum(pNtk), pAbc->pCex->iPo );
    else
    {
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
        Gia_Man_t * pGia = Gia_ManFromAigSimple( pAig );
//        if ( !Gia_ManVerifyCex( pGia, pAbc->pCex, 0 ) )
        int iPoOld = pAbc->pCex->iPo;
        pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pGia, pAbc->pCex, 0 );
        Gia_ManStop( pGia );
        if ( pAbc->pCex->iPo == -1 )
        {
            pAbc->pCex->iPo = iPoOld;
            Abc_Print( -1, "Main AIG: The cex does not fail any outputs.\n" );
            return 0;
        }
        else if ( iPoOld != pAbc->pCex->iPo )
            Abc_Print( 0, "Main AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
        // perform minimization
        vCexNew = Saig_ManCexMinPerform( pAig, pAbc->pCex );
        Aig_ManStop( pAig );
        Abc_CexFree( vCexNew );
//        Abc_FrameReplaceCex( pAbc, &vCexNew );

//        Abc_Print( 1,"Implementation of this command is not finished.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: cexmin [-CR num] [-vh]\n" );
    Abc_Print( -2, "\t         reduces the length of the counter-example\n" );
    Abc_Print( -2, "\t-C num : the maximum number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-R num : the number of minimization rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParSim_t Pars, * pPars = &Pars;
    char * pFileName = NULL;
    int c;
    Gia_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWNTImvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIters < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->RandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->RandSeed < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            if ( pFileName == NULL )
                goto usage;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sim(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pFileName != NULL )
    {
        extern void Gia_ManSimSimulatePattern( Gia_Man_t * p, char * pFileIn, char * pFileOut );
        char pFileNameOut[1000];
        char * pNameGeneric = Extra_FileNameGeneric(pFileName);
        assert( strlen(pNameGeneric) < 900 );
        sprintf( pFileNameOut, "%s_out.%s", pNameGeneric, Extra_FileNameExtension(pFileName) );
        ABC_FREE( pNameGeneric );
        Gia_ManSimSimulatePattern( pAbc->pGia, pFileName, pFileNameOut );
        return 1;
    }

    pAbc->nFrames = -1;
    if ( Gia_ManSimSimulate( pAbc->pGia, pPars ) )
        pAbc->Status =  0;
    else
        pAbc->Status = -1;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
//    if ( pLogFileName )
//        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&sim" );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim [-FWNT num] [-mvh] -I <file>\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t         (if candidate equivalences are defined, performs refinement)\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", pPars->nIters );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", pPars->RandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-I file: (optional) file with input patterns (one line per frame, as many as PIs)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sim2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManSimTwo( Gia_Man_t * p0, Gia_Man_t * p1, int nWords, int nRounds, int TimeLimit, int fVerbose );
    Gia_Man_t * pGias[2]; FILE * pFile;
    char ** pArgvNew; int nArgcNew;
    int c, RetValue = 0, fVerbose = 0, nWords = 16, nRounds = 10, RandSeed = 1, TimeLimit = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WRNTvh" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            RandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( RandSeed < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeLimit < 0 )
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
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew > 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Cec(): Wrong number of command-line arguments.\n" );
        return 1;
    }
    if ( nArgcNew == 2 )
    {
        char * pFileNames[2] = { pArgvNew[0], pArgvNew[1] }, * pTemp;
        int n; 
        for ( n = 0; n < 2; n++ )
        {
            // fix the wrong symbol
            for ( pTemp = pFileNames[n]; *pTemp; pTemp++ )
                if ( *pTemp == '>' )
                    *pTemp = '\\';
            if ( (pFile = fopen( pFileNames[n], "r" )) == NULL )
            {
                Abc_Print( -1, "Cannot open input file \"%s\". ", pFileNames[n] );
                if ( (pFileNames[n] = Extra_FileGetSimilarName( pFileNames[n], ".aig", NULL, NULL, NULL, NULL )) )
                    Abc_Print( 1, "Did you mean \"%s\"?", pFileNames[n] );
                Abc_Print( 1, "\n" );
                return 1;
            }
            fclose( pFile );
            pGias[n] = Gia_AigerRead( pFileNames[n], 0, 0, 0 );
            if ( pGias[n] == NULL )
            {
                Abc_Print( -1, "Reading AIGER from file \"%s\" has failed.\n", pFileNames[n] );
                return 0;
            }
        }
    }
    else
    {
        char * FileName, * pTemp;
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cec(): There is no current AIG.\n" );
            return 1;
        }
        pGias[0] = pAbc->pGia;
        if ( nArgcNew == 1 )
            FileName = pArgvNew[0];
        else
        {
            assert( nArgcNew == 0 );
            if ( pAbc->pGia->pSpec == NULL )
            {
                Abc_Print( -1, "File name is not given on the command line.\n" );
                return 1;
            }
            FileName = pAbc->pGia->pSpec;
        }
        // fix the wrong symbol
        for ( pTemp = FileName; *pTemp; pTemp++ )
            if ( *pTemp == '>' )
                *pTemp = '\\';
        if ( (pFile = fopen( FileName, "r" )) == NULL )
        {
            Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
            if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", NULL, NULL, NULL, NULL )) )
                Abc_Print( 1, "Did you mean \"%s\"?", FileName );
            Abc_Print( 1, "\n" );
            return 1;
        }
        fclose( pFile );
        pGias[1] = Gia_AigerRead( FileName, 0, 0, 0 );
        if ( pGias[1] == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 0;
        }
    }
    if ( Gia_ManCiNum(pGias[0]) != Gia_ManCiNum(pGias[1]) )
    {
        Abc_Print( -1, "The number of CIs does not match.\n" );
        return 1;
    }
    if ( Gia_ManCoNum(pGias[0]) != Gia_ManCoNum(pGias[1]) )
    {
        Abc_Print( -1, "The number of COs does not match.\n" );
        return 1;
    }
    RetValue = Gia_ManSimTwo( pGias[0], pGias[1], nWords, nRounds, TimeLimit, fVerbose );
    if ( pGias[0] != pAbc->pGia )
        Gia_ManStopP( &pGias[0] );
    Gia_ManStopP( &pGias[1] );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim2 [-WRNT num] [-vh] <file1.aig> <file2.aig>\n" );
    Abc_Print( -2, "\t         performs random of two circuits\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", nWords );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", RandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", TimeLimit );
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
int Abc_CommandAbc9Sim3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Ssw_RarSimulateGia( Gia_Man_t * p, Ssw_RarPars_t * pPars );
    Ssw_RarPars_t Pars, * pPars = &Pars;
    int c;
    Ssw_RarSetDefaultParams( pPars );
    // parse command line
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRSNTGgvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBinSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBinSize < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRestart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRestart < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRandSeed < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOut < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOutGap = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOutGap < 0 )
                goto usage;
            break;
        case 'g':
            pPars->fUseFfGrouping ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sim3(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sim3(): This command works only for sequential AIGs.\n" );
        return 0;
    }
    pAbc->Status = Ssw_RarSimulateGia( pAbc->pGia, pPars );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim3 [-FWBRNT num] [-gvh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n",       pPars->nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",        pPars->nWords );
    Abc_Print( -2, "\t-B num : the number of flops in one bin [default = %d]\n",         pPars->nBinSize );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n",        pPars->nRounds );
    Abc_Print( -2, "\t-S num : the number of rounds before a restart [default = %d]\n",  pPars->nRestart );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n",  pPars->nRandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n",   pPars->TimeOut );
    Abc_Print( -2, "\t-g     : toggle heuristic flop grouping [default = %s]\n",    pPars->fUseFfGrouping? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",    pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MLGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManDumpFiles( Gia_Man_t * p, int nCexesT, int nCexesV, int Seed, char * pFileName );
    extern void Gia_ManDumpPlaFiles( Gia_Man_t * p, int nCexesT, int nCexesV, int Seed, char * pFileName );
    int c, Seed = 0, nWords = 10, fBinData = 0, fVerbose = 0;
    char * pFileName = NULL;
    char ** pArgvNew;
    int nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WSbvh" ) ) != EOF )
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
        case 'b':
            fBinData ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9MLGen(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9MLGen(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew == 0 )
        printf( "Default file names will be used.\n" );
    else
        pFileName = pArgvNew[0];
    if ( nArgcNew != 0 && nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    if ( fBinData )
        Gia_ManDumpFiles( pAbc->pGia, nWords, nWords, Seed, pFileName );
    else
        Gia_ManDumpPlaFiles( pAbc->pGia, nWords, nWords, Seed, pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: &mlgen [-WS num] [-bvh] <file>\n" );
    Abc_Print( -2, "\t         generates data files for machine learning\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", nWords );
    Abc_Print( -2, "\t-S num : the random seed for simulation data (num < 10000) [default = %d]\n", Seed );
    Abc_Print( -2, "\t-b     : toggle using binary data files [default = %s]\n", fBinData? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file to store the simulation info\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MLTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManTestOneFile( Gia_Man_t * p, char * pFileName, char * pDumpFile );
    int c, fVerbose = 0;
    char * pDumpFile = NULL;
    char ** pArgvNew;
    int nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a file name.\n" );
                goto usage;
            }
            pDumpFile = argv[globalUtilOptind];
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
        Abc_Print( -1, "Abc_CommandAbc9MLTest(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9MLTest(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9MLTest(): Expecting data file name on the command line.\n" );
        return 0;
    }
    Gia_ManTestOneFile( pAbc->pGia, pArgvNew[0], pDumpFile );
    return 0;

usage:
    Abc_Print( -2, "usage: &mltest [-vh] [-D file] <file>\n" );
    Abc_Print( -2, "\t          testing command for machine learning data\n" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t-D file : file name to dump statistics [default = none]\n" );
    Abc_Print( -2, "\tfile    : file with input simulation info\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Iwls21Test( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManTestWordFile( Gia_Man_t * p, char * pFileName, char * pDumpFile, int fVerbose );
    int c, fVerbose = 0;
    char * pDumpFile = NULL;
    char ** pArgvNew;
    int nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a file name.\n" );
                goto usage;
            }
            pDumpFile = argv[globalUtilOptind];
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
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew == 2 )
    {
        Gia_Man_t * pAig = Gia_AigerRead( pArgvNew[0], 0, 0, 0 );
        if ( pAig == NULL )
        {
            Abc_Print( -1, "Reading AIGER from file \"%s\" has failed.\n", pArgvNew[0] );
            return 0;
        }
        if ( Gia_ManRegNum(pAig) > 0 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): This command works only for combinational AIGs.\n" );
            return 0;
        }
        if ( Gia_ManCoNum(pAig) != 10 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): Expecting an AIG with 10 outputs.\n" );
            return 0;
        }
        Gia_ManTestWordFile( pAig, pArgvNew[1], pDumpFile, fVerbose );
        Gia_ManStop( pAig );
        return 0;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManCoNum(pAbc->pGia) != 10 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): Expecting an AIG with 10 outputs.\n" );
        return 0;
    }
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): Expecting data file name on the command line.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iwls21Test(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
    Gia_ManTestWordFile( pAbc->pGia, pArgvNew[0], pDumpFile, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &iwls21test [-vh] [-D file] <file1> <file2>\n" );
    Abc_Print( -2, "\t          this command evaluates AIG for 2021 IWLS ML+LS Contest\n" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t-D file : file name to dump statistics [default = none]\n" );
    Abc_Print( -2, "\tfile1   : file with input AIG (or \"&read <file1.aig>; &iwls21test <file2>\" can be used)\n");
    Abc_Print( -2, "\tfile2   : file with CIFAR10 image data (https://www.cs.toronto.edu/~kriz/cifar.html)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fOutputs = 0, nWords = 4, fTruth = 0, fReverse = 0, fVerbose = 0;
    char ** pArgvNew;
    int nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Wtrovh" ) ) != EOF )
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
        case 't':
            fTruth ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;            
        case 'o':
            fOutputs ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9ReadSim(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReadSim(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    if ( fTruth )
    {
        if ( Gia_ManCiNum(pAbc->pGia) > 20 )
        {
            Abc_Print( -1, "Abc_CommandAbc9ReadSim(): More than 20 inputs.\n" );
            return 1;
        }
        Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
        pAbc->pGia->vSimsPi = fReverse ? Vec_WrdStartTruthTablesRev( Gia_ManCiNum(pAbc->pGia) ) : Vec_WrdStartTruthTables( Gia_ManCiNum(pAbc->pGia) );
        Vec_WrdFreeP( &pAbc->pGia->vSimsPo );
        pAbc->pGia->vSimsPo = Gia_ManSimPatSimOut( pAbc->pGia, pAbc->pGia->vSimsPi, 1 );
        return 0;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    if ( fOutputs )
    {
        Vec_WrdFreeP( &pAbc->pGia->vSimsPo );
        pAbc->pGia->vSimsPo = Vec_WrdReadHex( pArgvNew[0], NULL, 1 );
        if ( Vec_WrdSize(pAbc->pGia->vSimsPo) % Gia_ManCoNum(pAbc->pGia) != 0 )
        {
            Vec_WrdFreeP( &pAbc->pGia->vSimsPo );
            Abc_Print( -1, "File size (%d words) does not match the number of AIG inputs (%d %% %d != %d).\n", 
                Vec_WrdSize(pAbc->pGia->vSimsPo), Vec_WrdSize(pAbc->pGia->vSimsPo), Gia_ManCiNum(pAbc->pGia), 
                Vec_WrdSize(pAbc->pGia->vSimsPo) % Gia_ManCiNum(pAbc->pGia) );
            return 1;
        }
        pAbc->pGia->nSimWords = Vec_WrdSize(pAbc->pGia->vSimsPo) / Gia_ManCoNum(pAbc->pGia);
    }
    else
    {
        Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
        pAbc->pGia->vSimsPi = Vec_WrdReadHex( pArgvNew[0], NULL, 1 );
        if ( Vec_WrdSize(pAbc->pGia->vSimsPi) % Gia_ManCiNum(pAbc->pGia) != 0 )
        {
            Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
            Abc_Print( -1, "File size (%d words) does not match the number of AIG inputs (%d %% %d != %d).\n", 
                Vec_WrdSize(pAbc->pGia->vSimsPi), Vec_WrdSize(pAbc->pGia->vSimsPi), Gia_ManCiNum(pAbc->pGia), 
                Vec_WrdSize(pAbc->pGia->vSimsPi) % Gia_ManCiNum(pAbc->pGia) );
            return 1;
        }
        pAbc->pGia->nSimWords = Vec_WrdSize(pAbc->pGia->vSimsPi) / Gia_ManCiNum(pAbc->pGia);
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &sim_read [-W num] [-trovh] <file>\n" );
    Abc_Print( -2, "\t         reads simulation patterns from file\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", nWords );
    Abc_Print( -2, "\t-t     : toggle creating exhaustive simulation info [default = %s]\n", fTruth? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle reversing MSB and LSB input variables [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle reading output information [default = %s]\n", fOutputs? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file to store the simulation info\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9WriteSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fOutputs = 0, fTrans = 0, fBool = 0, fVerbose = 0;
    char ** pArgvNew;
    int nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "otbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'o':
            fOutputs ^= 1;
            break;
        case 't':
            fTrans ^= 1;
            break;
        case 'b':
            fBool ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9WriteSim(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9WriteSim(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    if ( (fOutputs ? pAbc->pGia->vSimsPo : pAbc->pGia->vSimsPi) == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9WriteSim(): Does not have simulation information available.\n" );
        return 0;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    if ( fOutputs )
    {
        Vec_Wrd_t * vTemp;
        int nWords = Vec_WrdSize(pAbc->pGia->vSimsPo) / Gia_ManCoNum(pAbc->pGia);
        assert( Vec_WrdSize(pAbc->pGia->vSimsPo) % Gia_ManCoNum(pAbc->pGia) == 0 );
        if ( fTrans )
        {
            int nSize = Vec_WrdSize(pAbc->pGia->vSimsPo);
            Vec_WrdFillExtra( pAbc->pGia->vSimsPo, nWords * 64 * ((Gia_ManCoNum(pAbc->pGia) + 63)/64), 0 );
            vTemp = Vec_WrdStart( Vec_WrdSize(pAbc->pGia->vSimsPo) );
            Extra_BitMatrixTransposeP( pAbc->pGia->vSimsPo, nWords, vTemp, (Gia_ManCoNum(pAbc->pGia) + 63)/64 );
            if ( fBool )
                Vec_WrdDumpBool( pArgvNew[0], vTemp, (Gia_ManCoNum(pAbc->pGia) + 63)/64, Gia_ManCoNum(pAbc->pGia), 1, 1 );
            else
                Vec_WrdDumpHex( pArgvNew[0], vTemp, (Gia_ManCoNum(pAbc->pGia) + 63)/64, 1 );
            Vec_WrdShrink( pAbc->pGia->vSimsPo, nSize );
            Vec_WrdFree( vTemp );
        }
        else
        {
            if ( fBool )
                Vec_WrdDumpBool( pArgvNew[0], pAbc->pGia->vSimsPo, nWords, Gia_ManCoNum(pAbc->pGia), 1, 1 );
            else
                Vec_WrdDumpHex( pArgvNew[0], pAbc->pGia->vSimsPo, nWords, 1 );
        }
    }
    else
    {
        Vec_Wrd_t * vTemp;
        int nWords = Vec_WrdSize(pAbc->pGia->vSimsPi) / Gia_ManCiNum(pAbc->pGia);
        assert( Vec_WrdSize(pAbc->pGia->vSimsPi) % Gia_ManCiNum(pAbc->pGia) == 0 );
        if ( fTrans )
        {
            int nSize = Vec_WrdSize(pAbc->pGia->vSimsPi);
            Vec_WrdFillExtra( pAbc->pGia->vSimsPi, nWords * 64 * ((Gia_ManCiNum(pAbc->pGia) + 63)/64), 0 );
            vTemp = Vec_WrdStart( Vec_WrdSize(pAbc->pGia->vSimsPi) );
            Extra_BitMatrixTransposeP( pAbc->pGia->vSimsPi, nWords, vTemp, (Gia_ManCiNum(pAbc->pGia) + 63)/64 );
            if ( fBool )
                Vec_WrdDumpBool( pArgvNew[0], vTemp, (Gia_ManCiNum(pAbc->pGia) + 63)/64, Gia_ManCiNum(pAbc->pGia), 1, 1 );
            else
                Vec_WrdDumpHex( pArgvNew[0], vTemp, (Gia_ManCiNum(pAbc->pGia) + 63)/64, 1 );
            Vec_WrdShrink( pAbc->pGia->vSimsPi, nSize );
            Vec_WrdFree( vTemp );
        }
        else
        {
            if ( fBool )
                Vec_WrdDumpBool( pArgvNew[0], pAbc->pGia->vSimsPi, nWords, Gia_ManCiNum(pAbc->pGia), 1, 1 );
            else
                Vec_WrdDumpHex( pArgvNew[0], pAbc->pGia->vSimsPi, nWords, 1 );
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &sim_write [-otbvh] <file>\n" );
    Abc_Print( -2, "\t         writes simulation patterns into a file\n" );
    Abc_Print( -2, "\t-o     : toggle writing output information [default = %s]\n", fOutputs? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle transposing the simulation information [default = %s]\n", fTrans? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle dumping in boolean vs hexadecimal notation [default = %s]\n", fBool? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file to store the simulation info\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PrintSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSimProfile( Gia_Man_t * pGia );
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "Abc_CommandAbc9PrintSim(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9PrintSim(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    if ( pAbc->pGia->vSimsPi == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PrintSim(): Simulation patterns are not defined.\n" );
        return 0;
    }
    Gia_ManSimProfile( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim_print [-vh]\n" );
    Abc_Print( -2, "\t         writes simulation patterns into a file\n" );
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
int Abc_CommandAbc9GenSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSimProfile( Gia_Man_t * pGia );
    extern void Gia_ManPatSatImprove( Gia_Man_t * pGia, int nWords, int fVerbose );
    extern void Gia_ManPatDistImprove( Gia_Man_t * p, int fVerbose );
    extern void Gia_ManPatRareImprove( Gia_Man_t * p, int RareLimit, int fVerbose );
    int c, nWords = 4, nRare = -1, fDist = 0, fSatBased = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WRsdvh" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRare = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRare < 0 )
                goto usage;
            break;
        case 's':
            fSatBased ^= 1;
            break;
        case 'd':
            fDist ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9GenSim(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenSim(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    if ( fSatBased )
    {
        if ( pAbc->pGia->vSimsPi == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9GenSim(): Does not have simulation information available.\n" );
            return 0;
        }
        Gia_ManPatSatImprove( pAbc->pGia, nWords, fVerbose );
    }
    else if ( fDist )
    {
        if ( pAbc->pGia->vSimsPi == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9GenSim(): Does not have simulation information available.\n" );
            return 0;
        }
        Gia_ManPatDistImprove( pAbc->pGia, fVerbose );
    }
    else if ( nRare >= 0 )
    {
        if ( pAbc->pGia->vSimsPi == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9GenSim(): Does not have simulation information available.\n" );
            return 0;
        }
        Gia_ManPatRareImprove( pAbc->pGia, nRare, fVerbose );
    }
    else
    {
        Abc_Random(1);
        Vec_WrdFreeP( &pAbc->pGia->vSimsPi );
        pAbc->pGia->vSimsPi = Vec_WrdStartRandom( Gia_ManCiNum(pAbc->pGia) * nWords );
        printf( "Generated %d random patterns (%d 64-bit data words) for each input of the AIG.\n", 64*nWords, nWords );
    }
    Gia_ManSimProfile( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim_gen [-WR num] [-sdvh]\n" );
    Abc_Print( -2, "\t         generates random simulation patterns\n" );
    Abc_Print( -2, "\t-W num : the number of 64-bit words of simulation info [default = %d]\n",            nWords );
    Abc_Print( -2, "\t-R num : the rarity parameter used to define scope [default = %d]\n",                nRare );
    Abc_Print( -2, "\t-s     : toggle using SAT-based improvement of available patterns [default = %s]\n", fSatBased? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle using one improvement of available patterns [default = %s]\n",       fDist? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",                      fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Resim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSim_t Pars, * pPars = &Pars;
    int c, RetValue;
    Cec_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 )
                goto usage;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Resim(): There is no AIG.\n" );
        return 1;
    }
    RetValue = Cec_ManSeqResimulateCounter( pAbc->pGia, pPars, pAbc->pCex );
    pAbc->Status  = RetValue ? 0 : -1;
    pAbc->nFrames = pAbc->pCex->iFrame;
//    Abc_FrameReplaceCex( pAbc, &pAbc->pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: &resim [-F num] [-mvh]\n" );
    Abc_Print( -2, "\t         resimulates equivalence classes using counter-example\n" );
    Abc_Print( -2, "\t-F num : the number of additinal frames to simulate [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Abc_CommandAbc9AdvGenSim]

  Description [This function calls SimGen tool]

  SideEffects []

  SeeAlso     []

***********************************************************************/

int Abc_CommandAbc9AdvGenSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Cec_SimGenSetParDefault( Cec_ParSimGen_t * pPars );
    extern Gia_Man_t * Cec_SimGenRun( Gia_Man_t * pAig, Cec_ParSimGen_t * pPars );

    Cec_ParSimGen_t ParsFra, * pPars = &ParsFra; Gia_Man_t * pTemp;
    int c;
    Cec_SimGenSetParDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "EOStiFwvV" ) ) != EOF )
    {
        switch ( c )
        {
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->expId = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->expId < 0 )
                goto usage;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->bitwidthOutgold = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->bitwidthOutgold <= 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSimWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSimWords <= 0 )
                goto usage;
            break;
        case 't':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-t\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->timeOutSim = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->timeOutSim <= 0 )
                goto usage;
            break;
        case 'i':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-i\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxIter = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxIter <= -2 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->pFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;  
        case 'w':
            pPars->fUseWatchlist = 1;
            break;
        case 'v':
            pPars->fVerbose = 1;
            break;
        case 'V':
            pPars->fVeryVerbose = 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Fraig(): There is no AIG.\n" );
        return 1;
    }
    
    pTemp = Cec_SimGenRun(pAbc->pGia, pPars );
    if ( pAbc->pGia->pCexSeq != NULL )
    {
        pAbc->Status  = 0;
        pAbc->nFrames = 0;
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &adv_sim_gen [-EOSsivV <num>] [-v] \n" );
    Abc_Print( -2, "\t         generates simulation patterns for combinational SAT sweeping\n" );
    Abc_Print( -2, "\t-E num : the experiment ID for different techniques [default = %d]\n", pPars->expId );
    Abc_Print( -2, "\t-O num : the bitwidth of the output gold [default = %d]\n", pPars->bitwidthOutgold );
    Abc_Print( -2, "\t-S num : the number of words in a round for random simulation [default = %d]\n", pPars->nSimWords );
    Abc_Print( -2, "\t-t num : the timeout value [default = %.0f]\n", pPars->timeOutSim);
    Abc_Print( -2, "\t-i num : the number of rounds of random simulation [default = %d]\n", pPars->nMaxIter );
    Abc_Print( -2, "\t-F file: the file name to dump the generated patterns  [default = none]\n");
    Abc_Print( -2, "\t-w     : activates the watchlist feature [default = %d]\n", pPars->fUseWatchlist);
    Abc_Print( -2, "\t-v     : verbose [default = %d]\n", pPars->fVerbose );
    Abc_Print( -2, "\t-V     : very verbose [default = %d]\n", pPars->fVeryVerbose );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LNetSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSimInfoPassTest( Gia_Man_t * p, char * pFileName, char * pFileName2, int fVerbose );
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Expecting two file names on the command line.\n" );
        return 1;
    }
    Gia_ManSimInfoPassTest( pAbc->pGia, argv[globalUtilOptind], argv[globalUtilOptind+1], fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &lnetsim [-vh] <file> <file2>\n" );
    Abc_Print( -2, "\t           performs specialized AIG simulation\n" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<file>   : input file name with simulation information\n");
    Abc_Print( -2, "\t<file2>  : output file name with simulation information\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LNetEval( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSimInfoEval( Gia_Man_t * p, char * pFileName, char * pFileName2, int nOuts, int fVerbose );
    int c, nOuts = -1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nOuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Expecting two file names on the command line.\n" );
        return 1;
    }
    Gia_ManSimInfoEval( pAbc->pGia, argv[globalUtilOptind], argv[globalUtilOptind+1], nOuts, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &lneteval [-O num] [-vh] <file> <file2>\n" );
    Abc_Print( -2, "\t           performs testing of the AIG on the simulation data\n" );
    Abc_Print( -2, "\t-O num   : the output group size [default = %d]\n",  nOuts );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<file>   : file name with simulation information\n");
    Abc_Print( -2, "\t<file2>  : file name with simulation information\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Era( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    int fUseCubes = 1;
    int fDumpFile = 0;
    int fMiter = 0;
    int nStatesMax = 1000000000;
    extern int Gia_ManCollectReachable( Gia_Man_t * pAig, int nStatesMax, int fMiter, int fDumpFile, int fVerbose );
    extern int Gia_ManArePerform( Gia_Man_t * pAig, int nStatesMax, int fMiter, int fVerbose );

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Smcdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nStatesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStatesMax < 0 )
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'c':
            fUseCubes ^= 1;
            break;
        case 'd':
            fDumpFile ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Era(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Era(): The network is combinational.\n" );
        return 1;
    }
    if ( !fUseCubes && Gia_ManPiNum(pAbc->pGia) > 12 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Era(): The number of PIs (%d) should be no more than 12 when cubes are not used.\n", Gia_ManPiNum(pAbc->pGia) );
        return 1;
    }
    if ( fUseCubes && !fDumpFile )
        pAbc->Status = Gia_ManArePerform( pAbc->pGia, nStatesMax, fMiter, fVerbose );
    else
        pAbc->Status = Gia_ManCollectReachable( pAbc->pGia, nStatesMax, fMiter, fDumpFile, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &era [-S num] [-mcdvh]\n" );
    Abc_Print( -2, "\t          explicit reachability analysis for small sequential AIGs\n" );
    Abc_Print( -2, "\t-S num  : the max number of states (num > 0) [default = %d]\n", nStatesMax );
    Abc_Print( -2, "\t-m      : stop when the miter output is 1 [default = %s]\n", fMiter? "yes": "no" );
    Abc_Print( -2, "\t-c      : use state cubes instead of state minterms [default = %s]\n", fUseCubes? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggle dumping STG into a file [default = %s]\n", fDumpFile? "yes": "no" );
    Abc_Print( -2, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9CexInfo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Bmc_CexTest( Gia_Man_t * p, Abc_Cex_t * pCex, int fVerbose );
    int c, fDualOut = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDualOut ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9CexInfo(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9CexInfo(): There is no CEX.\n" );
        return 1;
    }
    Bmc_CexTest( pAbc->pGia, pAbc->pCex, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &cexinfo [-vh]\n" );
    Abc_Print( -2, "\t         prints information about the current counter-example\n" );
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
int Abc_CommandAbc9FFTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ParFfSetDefault( Bmc_ParFf_t * p );
    extern void Gia_ManFaultTest( Gia_Man_t * p, Gia_Man_t * pG, Bmc_ParFf_t * pPars );
    Bmc_ParFf_t Pars, * pPars = &Pars;
    char * pFileName = NULL, * pFileName2 = NULL;
    Gia_Man_t * pGold = NULL;
    int c;
    Gia_ParFfSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ATNKSGFkbsfcdeunvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->Algo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Algo < 0 || pPars->Algo > 4 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterCheck = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterCheck < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCardConstr = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCardConstr <= 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->pFormStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileName2 = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'k':
            pPars->fNonStrict ^= 1;
            break;
        case 'b':
            pPars->fBasic ^= 1;
            break;
        case 's':
            pPars->fStartPats ^= 1;
            break;
        case 'f':
            pPars->fFfOnly ^= 1;
            break;
        case 'c':
            pPars->fCheckUntest ^= 1;
            break;
        case 'd':
            pPars->fDump ^= 1;
            break;
        case 'e':
            pPars->fDumpDelay ^= 1;
            break;
        case 'u':
            pPars->fDumpUntest ^= 1;
            break;
        case 'n':
            pPars->fDumpNewFaults ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // read string from file
    if ( pFileName2 )
    {
        if ( !strcmp( Extra_FileNameExtension(pFileName2), "blif" ) )
        {
            extern char * Gia_DeriveFormula( Gia_Man_t * pGia, char ** ppNamesIn );
            Abc_Ntk_t * pNtk2 = Io_Read( pFileName2, Io_ReadFileType(pFileName2), 1, 0 );
            Abc_Ntk_t * pNtk3 = Abc_NtkStrash( pNtk2, 0, 0, 0 );
            Gia_Man_t * pGia  = Abc_NtkClpGia( pNtk3 );
            char ** ppNamesIn = Abc_NtkCollectCioNames( pNtk2, 0 );
            if ( Gia_ManCoNum(pGia) == 1 )
                pPars->pFormStr = Gia_DeriveFormula( pGia, ppNamesIn );
            else
                printf( "The formula BLIF file contains the network with more one output.\n" );
            ABC_FREE( ppNamesIn );
            Gia_ManStop( pGia );
            Abc_NtkDelete( pNtk2 );
            Abc_NtkDelete( pNtk3 );
            if ( pPars->pFormStr == NULL )
                goto usage;
        }
        else
        {
            FILE * pFile = fopen( pFileName2, "r" );
            if ( pFile == NULL )
            {
                Abc_Print( -1, "Abc_CommandAbc9FFTest(): File name \"%s\" with formula is invalid.\n", pFileName2 );
                return 0;
            }
            pPars->pFormStr = Extra_FileRead(pFile);
            fclose( pFile );
            // skip spaces
            while ( 1 )
            {
                int Len = strlen(pPars->pFormStr);
                char Char = pPars->pFormStr[Len-1];
                if ( Char == ' ' || Char == '\n' || Char == '\r' || Char == '\t' || Char == -51 )
                    pPars->pFormStr[Len-1] = '\0';
                else
                    break;
            }
        }
        printf( "Using formula \"%s\" from file \"%s\".\n", pPars->pFormStr, pFileName2 );
    }
    if ( pPars->Algo == 0 && pPars->pFormStr == NULL )
    {
        Abc_Print( -1, "Formula string (-S <str>) should be selected when algorithm is 0 (-A 0).\n" );
        return 0;
    }
    if ( pPars->Algo != 0 && pPars->pFormStr != NULL )
    {
        Abc_Print( -1, "Algorithm should be 0 (-A 0) when formula string is selected (-S <str>).\n" );
        return 0;
    }
    // get the file name
    if ( argc == globalUtilOptind + 1 )
    {
        FILE * pFile;
        pPars->pFileName = argv[globalUtilOptind];
        pFile = fopen( pPars->pFileName, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open file \"%s\" with the input test patterns.\n", pPars->pFileName );
            return 0;
        }
        fclose( pFile );
    }
    // check other conditions
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9FFTest(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 && pPars->Algo == 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9FFTest(): For delay testing, AIG should be sequential.\n" );
        return 0;
    }
    // check if the file is valid
    if ( pFileName )
    {
        FILE * pFile = fopen( pFileName, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9FFTest(): File name \"%s\" with golden model is invalid.\n", pFileName );
            return 0;
        }
        fclose( pFile );
        pGold = Gia_AigerRead( pFileName, 0, 0, 0 );
        if ( pGold == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9FFTest(): Cannot read file \"%s\" with golden model.\n", pFileName );
            return 0;
        }
        if ( Gia_ManPiNum(pAbc->pGia) != Gia_ManPiNum(pGold) )
        {
            Gia_ManStop( pGold );
            Abc_Print( -1, "Abc_CommandAbc9FFTest(): Old model and gold model have different number of PIs.\n" );
            return 0;
        }
        if ( Gia_ManPoNum(pAbc->pGia) != Gia_ManPoNum(pGold) )
        {
            Gia_ManStop( pGold );
            Abc_Print( -1, "Abc_CommandAbc9FFTest(): Old model and gold model have different number of POs.\n" );
            return 0;
        }
        printf( "Entered spec AIG from file \"%s\".\n", pFileName );
    }
    Gia_ManFaultTest( pAbc->pGia, pGold ? pGold : pAbc->pGia, pPars );
    Gia_ManStopP( &pGold );
    if ( pFileName2 )
        ABC_FREE( pPars->pFormStr );
    return 0;

usage:
    Abc_Print( -2, "usage: &fftest [-ATNK num] [-kbsfcdeunvh] <file> [-GF file] [-S str]\n" );
    Abc_Print( -2, "\t          performs functional fault test generation\n" );
    Abc_Print( -2, "\t-A num  : selects fault model for all gates [default = %d]\n", pPars->Algo );
    Abc_Print( -2, "\t                0: fault model is not selected (use -S str)\n" );
    Abc_Print( -2, "\t                1: delay fault testing for sequential circuits\n" );
    Abc_Print( -2, "\t                2: traditional stuck-at fault: -S (((a&b)&~p)|q)\n" );
    Abc_Print( -2, "\t                3: complement fault: -S ((a&b)^p)\n" );
    Abc_Print( -2, "\t                4: functionally observable fault\n" );
    Abc_Print( -2, "\t-T num  : specifies approximate runtime limit in seconds [default = %d]\n",        pPars->nTimeOut );
    Abc_Print( -2, "\t-N num  : specifies iteration to check for fixed parameters [default = %d]\n",     pPars->nIterCheck );
    Abc_Print( -2, "\t-K num  : specifies cardinality constraint (num > 0) [default = unused]\n" );
    Abc_Print( -2, "\t-k      : toggles non-strict cardinality (n <= K, instead of n == K) [default = %s]\n",pPars->fNonStrict?  "yes": "no" );
    Abc_Print( -2, "\t-b      : toggles testing for single faults (the same as \"-K 1\") [default = %s]\n", pPars->fBasic?      "yes": "no" );
    Abc_Print( -2, "\t-s      : toggles starting with the all-0 and all-1 patterns [default = %s]\n",    pPars->fStartPats?  "yes": "no" );
    Abc_Print( -2, "\t-f      : toggles faults at flop inputs only with \"-A 1\" and \"-S str\" [default = %s]\n",          pPars->fFfOnly?     "yes": "no" );
    Abc_Print( -2, "\t-c      : toggles checking if there are untestable faults [default = %s]\n",       pPars->fCheckUntest? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggles dumping test patterns into file \"<file>_tests.txt\" [default = %s]\n", pPars->fDump?       "yes": "no" );
    Abc_Print( -2, "\t-e      : toggles dumping test pattern pairs (delay faults only) [default = %s]\n", pPars->fDumpDelay? "yes": "no" );
    Abc_Print( -2, "\t-u      : toggles dumping untestable faults into \"<file>_untest.txt\" [default = %s]\n", pPars->fDumpUntest? "yes": "no" );
    Abc_Print( -2, "\t-n      : toggles dumping faults not detected by a given test set [default = %s]\n", pPars->fDumpNewFaults? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n",                  pPars->fVerbose?    "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<file>  : (optional) file name with input test patterns\n\n");
    Abc_Print( -2, "\t-G file : (optional) file name with the golden model\n\n");
    Abc_Print( -2, "\t-F file : (optional) file name with the fault model in BLIF format\n");
    Abc_Print( -2, "\t-S str  : (optional) string representing the fault model\n");
    Abc_Print( -2, "\t          The following notations are used:\n");
    Abc_Print( -2, "\t            Functional variables: {a,b} (both a and b are always present)\n");
    Abc_Print( -2, "\t            Parameter variables: {p,q,r,s,t,u,v,w} (any number from 1 to 8)\n");
    Abc_Print( -2, "\t            Boolean operators: AND(&), OR(|), XOR(^), MUX(?:), NOT(~)\n");
    Abc_Print( -2, "\t            Parentheses should be used around each operator. Spaces not allowed.\n");
    Abc_Print( -2, "\t            Complement (~) is only allowed before variables (use DeMorgan law).\n");
    Abc_Print( -2, "\t            Examples:\n");
    Abc_Print( -2, "\t              (((a&b)&~p)|q)        stuck-at-0/1 at the output\n");
    Abc_Print( -2, "\t              (((a&~p)|q)&b)        stuck-at-0/1 at input a\n");
    Abc_Print( -2, "\t              (((a|p)&(b|q))&~r)    stuck-at-1 at the inputs and stuck-at-0 at the output\n");
    Abc_Print( -2, "\t              (((a&~p)&(b&~q))|r)   stuck-at-0 at the inputs and stuck-at-1 at the output\n");
    Abc_Print( -2, "\t              ((a&b)^p)             complement at the output\n");
    Abc_Print( -2, "\t              (((a^p)&(b^q))^r)     complement at the inputs and at the output\n");
    Abc_Print( -2, "\t              (a?(b?~s:r):(b?q:p))  functionally observable fault at the output\n");
    Abc_Print( -2, "\t              (p?(a|b):(a&b))       replace AND by OR\n");
    Abc_Print( -2, "\t           If the BLIF file is used for the formula with option \'-F\', following rules apply:\n");
    Abc_Print( -2, "\t              - the network should be combinational and have exactly one primary output\n");
    Abc_Print( -2, "\t              - input names should have only one character:\n");
    Abc_Print( -2, "\t                {a, b} (for functional variables)\n");
    Abc_Print( -2, "\t                {p,q,r,s,t,u,v,w} (for parameter variables)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Inse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Gia_ManInseTest( Gia_Man_t * p, Vec_Int_t * vInit, int nFrames, int nWords, int nTimeOut, int fSim, int fVerbose );
    int c, nFrames = 10, nWords = 1000, nTimeOut = 0, fSim = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWTsvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut < 0 )
                goto usage;
            break;
        case 's':
            fSim ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Inse(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Inse(): AIG is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vInitClasses != NULL )
    {
        Abc_Print( 1, "Abc_CommandAbc9Inse(): All-0 initial state is assumed.\n" );
        Vec_IntFreeP( &pAbc->pGia->vInitClasses );
    }
    pAbc->pGia->vInitClasses = Gia_ManInseTest( pAbc->pGia, NULL, nFrames, nWords, nTimeOut, fSim, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &inse [-FWT num] [-svh]\n" );
    Abc_Print( -2, "\t         experimental procedure\n" );
    Abc_Print( -2, "\t-F num : the number of timeframes [default = %d]\n",                    nFrames );
    Abc_Print( -2, "\t-W num : the number of machine words [default = %d]\n",                 nWords );
    Abc_Print( -2, "\t-T num : approximate global runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-s     : toggles using ternary simulation [default = %s]\n",            fSim?     "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",        fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Maxi( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Gia_ManMaxiTest( Gia_Man_t * p, Vec_Int_t * vInit, int nFrames, int nWords, int nTimeOut, int fSim, int fVerbose );
    Vec_Int_t * vTemp;
    int c, nFrames = 5, nWords = 1000, nTimeOut = 0, fSim = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWTsvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut < 0 )
                goto usage;
            break;
        case 's':
            fSim ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Maxi(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Maxi(): AIG is combinational.\n" );
        return 0;
    }
    pAbc->pGia->vInitClasses = Gia_ManMaxiTest( pAbc->pGia, vTemp = pAbc->pGia->vInitClasses, nFrames, nWords, nTimeOut, fSim, fVerbose );
    Vec_IntFreeP( &vTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &maxi [-FWT num] [-svh]\n" );
    Abc_Print( -2, "\t         experimental procedure\n" );
    Abc_Print( -2, "\t-F num : the number of timeframes [default = %d]\n",                    nFrames );
    Abc_Print( -2, "\t-W num : the number of machine words [default = %d]\n",                 nWords );
    Abc_Print( -2, "\t-T num : approximate global runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-s     : toggles using ternary simulation [default = %s]\n",            fSim?     "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",        fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PoXsim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Gia_ManPoXSim( Gia_Man_t * p, int nFrames, int fVerbose );
    int c, nFrames = 1000, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): AIG is combinational.\n" );
        return 0;
    }
    Vec_IntFreeP( &pAbc->vAbcObjIds );
    pAbc->vAbcObjIds = Gia_ManPoXSim( pAbc->pGia, nFrames, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &poxsim [-F num] [-vh]\n" );
    Abc_Print( -2, "\t         X-valued simulation of the multi-output sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of timeframes [default = %d]\n",                    nFrames );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",        fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9CexCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    return -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9CexMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Cex_t * pCexNew;
    int c;
    int iFrStart = 0;
    int iFrStop  = ABC_INFINITY;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FGvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrStop = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrStop < 0 )
                goto usage;
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

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }
    if ( pAbc->pCex2 == NULL )
    {
        Abc_Print( 1, "There is no saved cex.\n");
        return 0;
    }
    if ( iFrStop - iFrStart < pAbc->pCex->iFrame )
    {
        Abc_Print( 1, "Current CEX does not allow to shorten the saved CEX.\n");
        return 0;
    }
    pCexNew = Abc_CexMerge( pAbc->pCex2, pAbc->pCex, iFrStart, iFrStop );
    if ( pCexNew == NULL )
    {
        Abc_Print( 1, "Merging CEXes has failed.\n");
        return 0;
    }
    // replace the saved CEX
    ABC_FREE( pAbc->pCex2 );
    pAbc->pCex2 = pCexNew;
    return 0;

usage:
    Abc_Print( -2, "usage: &cexmerge [-FG num] [-vh]\n" );
    Abc_Print( -2, "\t         merges the current CEX into the saved one\n" );
    Abc_Print( -2, "\t         and sets the resulting CEX as the saved one\n" );
    Abc_Print( -2, "\t-F num : 0-based number of the starting frame [default = %d]\n", iFrStart );
    Abc_Print( -2, "\t-G num : 0-based number of the ending frame [default = %d]\n",   iFrStop );
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
int Abc_CommandAbc9CexMin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Cex_t * Gia_ManCexMin( Gia_Man_t * p, Abc_Cex_t * pCex, int iFrameStart, int nRealPis, int fJustMax, int fUseAll, int fVerbose );
    Abc_Cex_t * pCexNew;
    int iFrameStart = 0;
    int nRealPis = -1;
    int fJustMax = 1;
    int fUseAll = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FNjavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrameStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrameStart < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nRealPis = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRealPis < 0 )
                goto usage;
            break;
        case 'j':
            fJustMax ^= 1;
            break;
        case 'a':
            fUseAll ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9CexMin(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9CexMin(): The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9CexMin(): There is no counter-example.\n" );
        return 1;
    }
    pCexNew = Gia_ManCexMin( pAbc->pGia, pAbc->pCex, iFrameStart, nRealPis, fJustMax, fUseAll, fVerbose );
    if ( pCexNew )
        Abc_FrameReplaceCex( pAbc, &pCexNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &cexmin [-FN num] [-javh]\n" );
    Abc_Print( -2, "\t         minimizes a deep counter-example\n" );
    Abc_Print( -2, "\t-F num : starting timeframe for minimization [default = %d]\n", iFrameStart );
    Abc_Print( -2, "\t-N num : the number of real primary inputs [default = %d]\n", nRealPis );
    Abc_Print( -2, "\t-j     : toggle computing all justifying assignments [default = %s]\n", fJustMax? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using all terminal objects [default = %s]\n", fUseAll? "yes": "no" );
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
int Abc_CommandAbc9Cfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Extra_CommandCfs( Gia_Man_t * pGia, int Limit, int Reps, int UnseenUse, int RareUse, int fReplaceRare, int fConstSim, int fDagNodes, float FlipProb, int fVerbose );
    int Limit       =   0;
    int Reps        =   1;
    int UnseenUse   =   2;
    int RareUse     =   2;
    int fReplaceRare=   0;
    int fConstSim   =   0;
    int fDagNodes   =   0;
    float FlipProb  =   0;
    int c, fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LNURPrcdvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            Reps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Reps < 0 )
                goto usage;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by an integer.\n" );
                goto usage;
            }
            UnseenUse = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( UnseenUse < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            RareUse = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( RareUse < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            FlipProb = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( FlipProb < 0 )
                goto usage;
            break;
        case 'r':
            fReplaceRare ^= 1;
            break;
        case 'c':
            fConstSim ^= 1;
            break;
        case 'd':
            fDagNodes ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Cfs(): There is no AIG.\n" );
        return 1;
    }
    Extra_CommandCfs( pAbc->pGia, Limit, Reps, UnseenUse, RareUse, fReplaceRare, fConstSim, fDagNodes, FlipProb, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &cfs [-LNURPrcdvh]\n" );
    Abc_Print( -2, "\t          performs simulation\n" );
    Abc_Print( -2, "\t-L num  : the limit on the number of occurrences [default = %d]\n",  Limit );
    Abc_Print( -2, "\t-N num  : the number of repetions of each pattern [default = %d]\n", Reps );
    Abc_Print( -2, "\t-U num  : what to do with unseen patterns [default = %d]\n",         UnseenUse );
    Abc_Print( -2, "\t-R num  : what to do with rare patterns [default = %d]\n",           RareUse );
    Abc_Print( -2, "\t-P num  : base2-log of ramdom flip probability [default = %f]\n",    FlipProb );
    Abc_Print( -2, "\t-r      : toggle replacing rare patterns [default = %s]\n",          fReplaceRare? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggle inserting constants [default = %s]\n",              fConstSim? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggle using only DAG nodes [default = %s]\n",             fDagNodes? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n",     fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenCex( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_GenerateCexes( char * pFileName, Gia_Man_t * p, int nMaxTries, int nMinCexes, int fUseSim, int fUseSat, int fShort, int fBlif, int fVerbose, int fVeryVerbose );
    char * pFileName = (char *)"cexes.txt";
    int nMinCexes =  1;
    int nMaxTries = 10;
    int fUseSim   =  1;
    int fUseSat   =  1;
    int fShort    =  0;
    int fBlif     =  0;
    int fVerbose  =  0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CMFstcbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nMinCexes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMinCexes < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxTries = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxTries < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;     
        case 's':
            fUseSim ^= 1;
            break;
        case 't':
            fUseSat ^= 1;
            break;
        case 'c':
            fShort ^= 1;
            break;
        case 'b':
            fBlif ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): There is no AIG.\n" );
        return 0;
    }
    Gia_GenerateCexes( pFileName, pAbc->pGia, nMaxTries, nMinCexes, fUseSim, fUseSat, fShort, fBlif, fVerbose, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: &gencex [-CM num] [-F file] [-stcbvh]\n" );
    Abc_Print( -2, "\t          generates satisfying assignments for each output of the miter\n" );
    Abc_Print( -2, "\t-C num  : the number of satisfying assignments [default = %d]\n",      nMinCexes );
    Abc_Print( -2, "\t-M num  : the max simulation runs before using SAT [default = %d]\n",  nMaxTries );
    Abc_Print( -2, "\t-F file : the output file name [default = %s]\n",                      pFileName );
    Abc_Print( -2, "\t-s      : toggles using reverse simulation [default = %s]\n",          fUseSim  ? "yes": "no" );
    Abc_Print( -2, "\t-t      : toggles using SAT solving [default = %s]\n",                 fUseSat  ? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggles outputing care literals only [default = %s]\n",      fShort   ? "yes": "no" );
    Abc_Print( -2, "\t-b      : toggles outputing the BLIF file [default = %s]\n",           fBlif    ? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n",      fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
