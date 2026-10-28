/**CFile****************************************************************

  FileName    [abcLogic.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Boolean logic processing.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "opt/fxu/fxu.h"
#include "opt/fxch/Fxch.h"
#include "opt/cut/cut.h"
#include "bool/kit/kit.h"
#include "bool/rpo/rpo.h"
#include "map/cov/cov.h"
#include "opt/nwk/nwkMerge.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandCollapse               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSatClp                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMulti                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRenode                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFastExtract            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFxch                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEliminate              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDisjoint               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSparsify               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLogicPush              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMerge                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestDec                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestNpn                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestRPO                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestTruth              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestSupp               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtract                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandVarMin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandReorder                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBidec                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxes                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCubes                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExpand                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSplitSop               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCut                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEspresso               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCover                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInter                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQuaVar                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQuaRel                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSenseInput             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNpnLoad                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNpnSave                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandICut                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdSave                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdLoad                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdFree                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdPs                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdMatch               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdMerge               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDsdFilter              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dsd                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Bidec              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Fx                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Extract            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sopb               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dsdb               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9DecGraph           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9QVar               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatFx              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatClp             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Esop               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Exorcism           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Odc                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9FunAbs             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9DsdInfo            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9FunTrace           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cuts               ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers boolean logic processing commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitLogic( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "clp",           Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "collapse",      Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "satclp",        Abc_CommandSatClp,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "multi",         Abc_CommandMulti,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "renode",        Abc_CommandRenode,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fx",            Abc_CommandFastExtract,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fxch",          Abc_CommandFxch,             1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "eliminate",     Abc_CommandEliminate,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "dsd",           Abc_CommandDisjoint,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "sparsify",      Abc_CommandSparsify,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "logicpush",     Abc_CommandLogicPush,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "merge",         Abc_CommandMerge,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "testdec",       Abc_CommandTestDec,          0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "testnpn",       Abc_CommandTestNpn,          0 );
    Cmd_CommandAdd( pAbc, "LogiCS",       "testrpo",       Abc_CommandTestRPO,          0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "testtruth",     Abc_CommandTestTruth,        0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "testsupp",      Abc_CommandTestSupp,         0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "extract",       Abc_CommandExtract,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "varmin",        Abc_CommandVarMin,           0 );
    Cmd_CommandAdd( pAbc, "Various",      "reorder",       Abc_CommandReorder,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "bidec",         Abc_CommandBidec,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "muxes",         Abc_CommandMuxes,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "cubes",         Abc_CommandCubes,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "expand",        Abc_CommandExpand,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "splitsop",      Abc_CommandSplitSop,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "cut",           Abc_CommandCut,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "espresso",      Abc_CommandEspresso,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "cover",         Abc_CommandCover,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "inter",         Abc_CommandInter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "qvar",          Abc_CommandQuaVar,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "qrel",          Abc_CommandQuaRel,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "senseinput",    Abc_CommandSenseInput,       1 );
    Cmd_CommandAdd( pAbc, "Various",      "npnload",       Abc_CommandNpnLoad,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "npnsave",       Abc_CommandNpnSave,          0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "icut",          Abc_CommandICut,             0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_save",      Abc_CommandDsdSave,          0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_load",      Abc_CommandDsdLoad,          0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_free",      Abc_CommandDsdFree,          0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_ps",        Abc_CommandDsdPs,            0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_match",     Abc_CommandDsdMatch,         0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_merge",     Abc_CommandDsdMerge,         0 );
    Cmd_CommandAdd( pAbc, "DSD manager",  "dsd_filter",    Abc_CommandDsdFilter,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dsd",          Abc_CommandAbc9Dsd,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bidec",        Abc_CommandAbc9Bidec,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&fx",           Abc_CommandAbc9Fx,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&extract",      Abc_CommandAbc9Extract,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sopb",         Abc_CommandAbc9Sopb,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dsdb",         Abc_CommandAbc9Dsdb,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dg"          , Abc_CommandAbc9DecGraph,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&qvar",         Abc_CommandAbc9QVar,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&satfx",        Abc_CommandAbc9SatFx,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&satclp",       Abc_CommandAbc9SatClp,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&esop",         Abc_CommandAbc9Esop,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&exorcism",     Abc_CommandAbc9Exorcism,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&odc",          Abc_CommandAbc9Odc,                    0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&funabs",       Abc_CommandAbc9FunAbs,                 0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&dsdinfo",      Abc_CommandAbc9DsdInfo,                0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&funtrace",     Abc_CommandAbc9FunTrace,               0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&cuts",         Abc_CommandAbc9Cuts,                   0 );
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
int Abc_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fVerbose;
    int fBddSizeMax;
    int fDualRail;
    int fReorder;
    int fReverse;
    int fDumpOrder;
    int c;
    char * pLogFileName = NULL;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fVerbose = 0;
    fReorder = 1;
    fReverse = 0;
    fDualRail = 0;
    fDumpOrder = 0;
    fBddSizeMax = ABC_INFINITY;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BLrodxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            fBddSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fBddSizeMax < 0 )
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
        case 'r':
            fReorder ^= 1;
            break;
        case 'o':
            fReverse ^= 1;
            break;
        case 'd':
            fDualRail ^= 1;
            break;
        case 'x':
            fDumpOrder ^= 1;
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

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fReverse, fDumpOrder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fReverse, fDumpOrder, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Collapsing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    if ( pLogFileName )
    {
        pAbc->pCex = NULL;
        pAbc->nFrames = -1;
        if ( Abc_NtkNodeNum(pNtkRes) == 0 ) 
            pAbc->Status =  1; // UNSAT
        else
            pAbc->Status = -1; // UNDEC
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "collapse" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: collapse [-B <num>] [-L file] [-rodxvh]\n" );
    Abc_Print( -2, "\t          collapses the network by constructing global BDDs\n" );
    Abc_Print( -2, "\t-B <num>: limit on live BDD nodes during collapsing [default = %d]\n", fBddSizeMax );
    Abc_Print( -2, "\t-L file : the log file name [default = %s]\n",  pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r      : toggles dynamic variable reordering [default = %s]\n", fReorder? "yes": "no" );
    Abc_Print( -2, "\t-o      : toggles reverse variable ordering [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggles dual-rail collapsing mode [default = %s]\n", fDualRail? "yes": "no" );
    Abc_Print( -2, "\t-x      : toggles dumping file \"order.txt\" with variable order [default = %s]\n", fDumpOrder? "yes": "no" );
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
int Abc_CommandSatClp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int nCubeLim   =        0;
    int nBTLimit   =  1000000;
    int nCostMax   = 20000000;
    int fCanon     = 0;
    int fReverse   = 0;
    int fCnfShared = 0;
    int fVerbose   = 0;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CLZcrsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubeLim < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
                goto usage;
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
                goto usage;
            }
            nCostMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCostMax < 0 )
                goto usage;
            break;
        case 'c':
            fCanon ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;
        case 's':
            fCnfShared ^= 1;
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

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCollapseSat( pNtk, nCubeLim, nBTLimit, nCostMax, fCanon, fReverse, fCnfShared, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes = Abc_NtkCollapseSat( pNtk, nCubeLim, nBTLimit, nCostMax, fCanon, fReverse, fCnfShared, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Collapsing has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: satclp [-CLZ num] [-crsvh]\n" );
    Abc_Print( -2, "\t         performs SAT based collapsing\n" );
    Abc_Print( -2, "\t-C num : the limit on the SOP size of one output [default = %d]\n",              nCubeLim );
    Abc_Print( -2, "\t-L num : the limit on the number of conflicts in one SAT call [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-Z num : the limit on the cost of the largest output [default = %d]\n",          nCostMax );
    Abc_Print( -2, "\t-c     : toggles using canonical ISOP computation [default = %s]\n",             fCanon? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles using reverse veriable ordering [default = %s]\n",              fReverse? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles shared CNF computation (non-canonical only) [default = %s]\n",  fCnfShared? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",                 fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMulti( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nThresh, nFaninMax, c;
    int fCnf;
    int fMulti;
    int fSimple;
    int fFactor;
    extern Abc_Ntk_t * Abc_NtkMulti( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple, int fFactor );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nThresh   =  1;
    nFaninMax = 20;
    fCnf      =  0;
    fMulti    =  1;
    fSimple   =  0;
    fFactor   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TFmcsfh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nThresh = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nThresh < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFaninMax < 0 )
                goto usage;
            break;
        case 'c':
            fCnf ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 's':
            fSimple ^= 1;
            break;
        case 'f':
            fFactor ^= 1;
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
        Abc_Print( -1, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkMulti( pNtk, nThresh, nFaninMax, fCnf, fMulti, fSimple, fFactor );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: multi [-TF <num>] [-msfch]\n" );
    Abc_Print( -2, "\t          transforms an AIG into a logic network by creating larger nodes\n" );
    Abc_Print( -2, "\t-F <num>: the maximum fanin size after renoding [default = %d]\n", nFaninMax );
    Abc_Print( -2, "\t-T <num>: the threshold for AIG node duplication [default = %d]\n", nThresh );
    Abc_Print( -2, "\t          (an AIG node is the root of a new node after renoding\n" );
    Abc_Print( -2, "\t          if this leads to duplication of no more than %d AIG nodes,\n", nThresh );
    Abc_Print( -2, "\t          that is, if [(numFanouts(Node)-1) * size(MFFC(Node))] <= %d)\n", nThresh );
    Abc_Print( -2, "\t-m      : creates multi-input AND graph [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-s      : creates a simple AIG (no renoding) [default = %s]\n", fSimple? "yes": "no" );
    Abc_Print( -2, "\t-f      : creates a factor-cut network [default = %s]\n", fFactor? "yes": "no" );
    Abc_Print( -2, "\t-c      : performs renoding to derive the CNF [default = %s]\n", fCnf? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRenode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nLutSize, nCutsMax, c;
    int nFlowIters, nAreaIters;
    int fArea;
    int fUseBdds;
    int fUseSops;
    int fUseCnfs;
    int fUseMv;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkRenode( Abc_Ntk_t * pNtk, int nLutSize, int nCutsMax, int nFlowIters, int nAreaIters, int fArea, int fUseBdds, int fUseSops, int fUseCnfs, int fUseMv, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nLutSize   =  8;
    nCutsMax   =  4;
    nFlowIters =  1;
    nAreaIters =  1;
    fArea      =  0;
    fUseBdds   =  0;
    fUseSops   =  0;
    fUseCnfs   =  0;
    fUseMv     =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFAabscivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFlowIters < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nAreaIters < 0 )
                goto usage;
            break;
        case 'a':
            fArea ^= 1;
            break;
        case 'b':
            fUseBdds ^= 1;
            break;
        case 's':
            fUseSops ^= 1;
            break;
        case 'c':
            fUseCnfs ^= 1;
            break;
        case 'i':
            fUseMv ^= 1;
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

    if ( fUseBdds + fUseSops + fUseCnfs + fUseMv > 1 )
    {
        Abc_Print( -1, "Cannot optimize two parameters at the same time.\n" );
        return 1;
    }

    if ( nLutSize < 2 || nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", nLutSize );
        return 1;
    }

    if ( nCutsMax < 1 || nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkRenode( pNtk, nLutSize, nCutsMax, nFlowIters, nAreaIters, fArea, fUseBdds, fUseSops, fUseCnfs, fUseMv, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: renode [-KCFA <num>] [-sbciav]\n" );
    Abc_Print( -2, "\t          transforms the AIG into a logic network with larger nodes\n" );
    Abc_Print( -2, "\t          while minimizing the number of FF literals of the node SOPs\n" );
    Abc_Print( -2, "\t-K <num>: the max cut size for renoding (2 < num < %d) [default = %d]\n", IF_MAX_FUNC_LUTSIZE+1, nLutSize );
    Abc_Print( -2, "\t-C <num>: the max number of cuts used at a node (0 < num < 2^12) [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-F <num>: the number of area flow recovery iterations (num >= 0) [default = %d]\n", nFlowIters );
    Abc_Print( -2, "\t-A <num>: the number of exact area recovery iterations (num >= 0) [default = %d]\n", nAreaIters );
    Abc_Print( -2, "\t-s      : toggles minimizing SOP cubes instead of FF lits [default = %s]\n", fUseSops? "yes": "no" );
    Abc_Print( -2, "\t-b      : toggles minimizing BDD nodes instead of FF lits [default = %s]\n", fUseBdds? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggles minimizing CNF clauses instead of FF lits [default = %s]\n", fUseCnfs? "yes": "no" );
    Abc_Print( -2, "\t-i      : toggles minimizing MV-SOP instead of FF lits [default = %s]\n", fUseMv? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggles area-oriented mapping [default = %s]\n", fArea? "yes": "no" );
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
int Abc_CommandFastExtract( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkFxPerform( Abc_Ntk_t * pNtk, int nNewNodesMax, int nLitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Fxu_Data_t Params, * p = &Params;
    int c, fNewAlgo = 1;
    int nPairsLimit = 1000000000;
    // set the defaults
    Abc_NtkSetDefaultFxParams( p );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "SDNWMPsdzcnxvwh")) != EOF )
    {
        switch (c)
        {
            case 'S':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nSingleMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nSingleMax < 0 )
                    goto usage;
                break;
            case 'D':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nPairsMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nPairsMax < 0 )
                    goto usage;
                break;
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nNodesExt = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nNodesExt < 0 )
                    goto usage;
                break;
            case 'W':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->WeightMin = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->WeightMin < 0 )
                    goto usage;
                break;
            case 'M':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->LitCountMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->LitCountMax < 0 )
                    goto usage;
                break;
            case 'P':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                    goto usage;
                }
                nPairsLimit = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nPairsLimit < 0 )
                    goto usage;
                break;
            case 's':
                p->fOnlyS ^= 1;
                break;
            case 'd':
                p->fOnlyD ^= 1;
                break;
            case 'z':
                p->fUse0 ^= 1;
                break;
            case 'c':
                p->fUseCompl ^= 1;
                break;
            case 'n':
                fNewAlgo ^= 1;
                break;
            case 'x':
                p->fCanonDivs ^= 1;
                break;
            case 'v':
                p->fVerbose ^= 1;
                break;
            case 'w':
                p->fVeryVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkNodeNum(pNtk) == 0 || Abc_NtkPiNum(pNtk) == 0 )
    {
        Abc_Print( 0, "The network does not have internal nodes.\n" );
        return 0;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Fast extract can only be applied to a logic network (run \"renode\" or \"if\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Fast extract can only be applied to a logic network with SOP local functions (run \"bdd; sop\").\n" );
        return 1;
    }
    if ( Abc_NtkGetCubePairNum(pNtk) > nPairsLimit )
    {
        Abc_Print( -1, "Cannot perform \"fx\" because the number cube pairs exceeds the limit (%d).\n", nPairsLimit );
        return 1;
    }

    // the nodes to be merged are linked into the special linked list
    if ( fNewAlgo )
        Abc_NtkFxPerform( pNtk, p->nNodesExt, p->LitCountMax, p->fCanonDivs, p->fVerbose, p->fVeryVerbose );
    else
        Abc_NtkFastExtract( pNtk, p );
    Abc_NtkFxuFreeInfo( p );
    return 0;

usage:
    Abc_Print( -2, "usage: fx [-SDNWMP <num>] [-sdzcnxvwh]\n");
    Abc_Print( -2, "\t           performs unate fast extract on the current network\n");
    Abc_Print( -2, "\t-S <num> : max number of single-cube divisors to consider [default = %d]\n", p->nSingleMax );
    Abc_Print( -2, "\t-D <num> : max number of double-cube divisors to consider [default = %d]\n", p->nPairsMax );
    Abc_Print( -2, "\t-N <num> : max number of divisors to extract during this run [default = %d]\n", p->nNodesExt );
    Abc_Print( -2, "\t-W <num> : lower bound on the weight of divisors to extract [default = %d]\n", p->WeightMin );
    Abc_Print( -2, "\t-M <num> : upper bound on literal count of divisors to extract [default = %d]\n", p->LitCountMax );
    Abc_Print( -2, "\t-P <num> : skip \"fx\" if cube pair count exceeds this limit [default = %d]\n", nPairsLimit );
    Abc_Print( -2, "\t-s       : use only single-cube divisors [default = %s]\n", p->fOnlyS? "yes": "no" );
    Abc_Print( -2, "\t-d       : use only double-cube divisors [default = %s]\n", p->fOnlyD? "yes": "no" );
    Abc_Print( -2, "\t-z       : use zero-weight divisors [default = %s]\n", p->fUse0? "yes": "no" );
    Abc_Print( -2, "\t-c       : use complement in the binary case [default = %s]\n", p->fUseCompl? "yes": "no" );
    Abc_Print( -2, "\t-n       : use new implementation of fast extract [default = %s]\n", fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-x       : use only canonical divisors (AND, XOR, MUX) [default = %s]\n", p->fCanonDivs? "yes": "no" );
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", p->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : print additional information [default = %s]\n", p->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandFxch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkFxchPerform( Abc_Ntk_t * pNtk, int nMaxDivExt, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    int c,
        nMaxDivExt = 0,
        fVerbose = 0,
        fVeryVerbose = 0;

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Nvwh")) != EOF )
    {
        switch (c)
        {
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                nMaxDivExt = atoi( argv[globalUtilOptind] );
                globalUtilOptind++;

                if ( nMaxDivExt < 0 )
                    goto usage;
                break;

            case 'v':
                fVerbose ^= 1;
                break;

            case 'w':
                fVeryVerbose ^= 1;
                break;

            case 'h':
                goto usage;
                break;

            default:
                goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkNodeNum( pNtk ) == 0 )
    {
        Abc_Print( -1, "The network does not have internal nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic( pNtk ) )
    {
        Abc_Print( -1, "Fast extract can only be applied to a logic network (run \"renode\" or \"if\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsSopLogic( pNtk ) )
    {
        Abc_Print( -1, "Fast extract can only be applied to a logic network with SOP local functions (run \"bdd; sop\").\n" );
        return 1;
    }

    Abc_NtkFxchPerform( pNtk, nMaxDivExt, fVerbose, fVeryVerbose );

    return 0;

usage:
    Abc_Print( -2, "usage: fxch [-N <num>] [-svwh]\n");
    Abc_Print( -2, "\t           performs fast extract with cube hashing on the current network\n");
    Abc_Print( -2, "\t-N <num> : max number of divisors to extract during this run [default = unused]\n" );
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : print additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Bruno Schmitt from UFRGS in May 2016.\n" );
    Abc_Print( -2, "\t           The author can be contacted as boschmitt at inf.ufrgs.br\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEliminate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int ElimValue;
    int nMaxSize;
    int nIterMax;
    int fGreedy;
    int fReverse;
    int fSpecial;
    int fVerbose;
    int c;
    extern int Abc_NtkEliminate( Abc_Ntk_t * pNtk, int nMaxSize, int fReverse, int fVerbose );
    extern int Abc_NtkEliminate1( Abc_Ntk_t * pNtk, int ElimValue, int nMaxSize, int nIterMax, int fReverse, int fVerbose );
    extern int Abc_NtkEliminateSpecial( Abc_Ntk_t * pNtk, int nMaxSize, int fVerbose );

    // set the defaults
    ElimValue = -1;
    nMaxSize  = 12;
    nIterMax  =  1;
    fGreedy   =  0;
    fReverse  =  0;
    fSpecial  =  0;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "VNIgrsvh")) != EOF )
    {
        switch (c)
        {
            case 'V':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer that is -1 or larger.\n" );
                    goto usage;
                }
                ElimValue = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( ElimValue < -1 )
                    goto usage;
                break;
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nMaxSize = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nMaxSize <= 0 )
                    goto usage;
                break;
            case 'I':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nIterMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nIterMax <= 0 )
                    goto usage;
                break;
            case 'g':
                fGreedy ^= 1;
                break;
            case 'r':
                fReverse ^= 1;
                break;
            case 's':
                fSpecial ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network does not have internal nodes.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network (run \"renode\" or \"if\").\n" );
        return 1;
    }

    if ( fSpecial )
        Abc_NtkEliminateSpecial( pNtk, 1000, fVerbose );
    else if ( fGreedy )
        Abc_NtkEliminate( pNtk, nMaxSize, fReverse, fVerbose );
    else
        Abc_NtkEliminate1( pNtk, ElimValue, nMaxSize, nIterMax, fReverse, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: eliminate [-VNI <num>] [-grsvh]\n");
    Abc_Print( -2, "\t           traditional \"eliminate -1\", which collapses the node into its fanout\n");
    Abc_Print( -2, "\t           if the node's variable appears in the fanout's factored form only once\n");
    Abc_Print( -2, "\t-V <num> : the \"value\" parameter used by \"eliminate\" in SIS [default = %d]\n", ElimValue );
    Abc_Print( -2, "\t-N <num> : the maximum node support after collapsing [default = %d]\n", nMaxSize );
    Abc_Print( -2, "\t-I <num> : the maximum number of iterations [default = %d]\n", nIterMax );
    Abc_Print( -2, "\t-g       : toggle using greedy eliminate (without \"value\") [default = %s]\n", fGreedy? "yes": "no" );
    Abc_Print( -2, "\t-r       : use the reverse topological order [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle eliminating similar nodes [default = %s]\n", fSpecial? "yes": "no" );
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDisjoint( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkNew;
    int fGlobal, fRecursive, fVerbose, fPrint, fShort, c;

    extern Abc_Ntk_t * Abc_NtkDsdGlobal( Abc_Ntk_t * pNtk, int fVerbose, int fPrint, int fShort );
    extern int         Abc_NtkDsdLocal( Abc_Ntk_t * pNtk, int fVerbose, int fRecursive );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fGlobal    = 1;
    fRecursive = 0;
    fVerbose   = 0;
    fPrint     = 0;
    fShort     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "grvpsh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'g':
                fGlobal ^= 1;
                break;
            case 'r':
                fRecursive ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'p':
                fPrint ^= 1;
                break;
            case 's':
                fShort ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fGlobal )
    {
//        Abc_Print( 0, "Performing DSD of global functions of the network.\n" );
        // get the new network
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            pNtkNew = Abc_NtkStrash( pNtk, 0, 0, 0 );
            pNtkRes = Abc_NtkDsdGlobal( pNtkNew, fVerbose, fPrint, fShort );
            Abc_NtkDelete( pNtkNew );
        }
        else
        {
            pNtkRes = Abc_NtkDsdGlobal( pNtk, fVerbose, fPrint, fShort );
        }
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Global DSD has failed.\n" );
            return 1;
        }
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    else if ( fRecursive )
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            Abc_Print( -1, "This command is only applicable to logic BDD networks.\n" );
            return 1;
        }
        if ( fVerbose )
            Abc_Print( 1, "Performing recursive DSD and MUX decomposition of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            Abc_Print( -1, "Recursive DSD has failed.\n" );
    }
    else
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            Abc_Print( -1, "This command is only applicable to logic BDD networks (run \"bdd\").\n" );
            return 1;
        }
        if ( fVerbose )
            Abc_Print( 1, "Performing simple non-recursive DSD of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            Abc_Print( -1, "Simple DSD of local functions has failed.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd [-grvpsh]\n" );
    Abc_Print( -2, "\t     decomposes the network using disjoint-support decomposition\n" );
    Abc_Print( -2, "\t-g     : toggle DSD of global and local functions [default = %s]\n", fGlobal? "global": "local" );
    Abc_Print( -2, "\t-r     : toggle recursive DSD/MUX and simple DSD [default = %s]\n", fRecursive? "recursive DSD/MUX": "simple DSD" );
    Abc_Print( -2, "\t-v     : prints DSD statistics and runtime [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-p     : prints DSD structure to the standard output [default = %s]\n", fPrint? "yes": "no" );
    Abc_Print( -2, "\t-s     : use short PI names when printing DSD structure [default = %s]\n", fShort? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSparsify( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkSparsify( Abc_Ntk_t * pNtk, int nPerc, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkNew;
    int nPerc, fVerbose, c;
    // set defaults
    nPerc      = 10;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                nPerc = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nPerc < 1 || nPerc > 100 )
                    goto usage;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsBddLogic( pNtk ) )
    {
        Abc_Print( -1, "This command is only applicable to logic BDD networks (run \"bdd\").\n" );
        return 1;
    }
    if ( Abc_NtkCiNum(pNtk) > 16 )
    {
        Abc_Print( -1, "The number of primary inputs is more than 16.\n" );
        return 1;
    }
    pNtkNew = Abc_NtkSparsify( pNtk, nPerc, fVerbose );
    if ( pNtkNew == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: sparsify [-N num] [-vh]\n" );
    Abc_Print( -2, "\t           creates incompletely-specified function\n" );
    Abc_Print( -2, "\t-N <num> : the percentage of on-set and off-set minterms (1 <= num <= 100) [default = %d]\n", nPerc );
    Abc_Print( -2, "\t-v       : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLogicPush( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkOptPush( Abc_Ntk_t * pNtk, int nLutSize, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int nLutSize = 4;
    int fVerbose = 0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }
    nLutSize = Abc_MaxInt( nLutSize, Abc_NtkGetFaninMax(pNtk) );
    Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
    pNtkRes = Abc_NtkOptPush( pNtk, nLutSize, fVerbose );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: logicpush [-K num] [-vh]\n" );
    Abc_Print( -2, "\t           performs logic pushing to reduce structural bias\n" );
    Abc_Print( -2, "\t-K <num> : the LUT size used in the mapping [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Nwk_LMPars_t Pars, * pPars = &Pars;
    Vec_Int_t * vResult;
    int c;
    extern Vec_Int_t * Abc_NtkLutMerge( Abc_Ntk_t * pNtk, Nwk_LMPars_t * pPars );
    // set defaults
    memset( pPars, 0, sizeof(Nwk_LMPars_t) );
    pPars->nMaxLutSize    = 5;   // the max LUT size for merging (N=5)
    pPars->nMaxSuppSize   = 5;   // the max total support size after merging (S=5)
    pPars->nMaxDistance   = 3;   // the max number of nodes separating LUTs
    pPars->nMaxLevelDiff  = 2;   // the max difference in levels
    pPars->nMaxFanout     = 100; // the max number of fanouts to traverse
    pPars->fUseDiffSupp   = 0;   // enables the use of nodes with different support
    pPars->fUseTfiTfo     = 0;   // enables the use of TFO/TFO nodes as candidates
    pPars->fVeryVerbose   = 0;   // enables additional verbose output
    pPars->fVerbose       = 1;   // enables verbose output
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSDLFscvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLutSize < 2 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxSuppSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxSuppSize < 2 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxDistance = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxDistance < 2 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevelDiff = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevelDiff < 2 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxFanout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxFanout < 2 )
                goto usage;
            break;
        case 's':
            pPars->fUseDiffSupp ^= 1;
            break;
        case 'c':
            pPars->fUseTfiTfo ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
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
    if ( pNtk == NULL || !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Abc_CommandMerge(): There is no mapped network to merge LUTs.\n" );
        return 1;
    }

    vResult = Abc_NtkLutMerge( pNtk, pPars );
    Vec_IntFree( vResult );
    return 0;

usage:
    Abc_Print( -2, "usage: merge [-NSDLF <num>] [-scwvh]\n" );
    Abc_Print( -2, "\t           creates pairs of topologically-related LUTs\n" );
    Abc_Print( -2, "\t-N <num> : the max LUT size for merging (1 < num) [default = %d]\n", pPars->nMaxLutSize );
    Abc_Print( -2, "\t-S <num> : the max total support size after merging (1 < num) [default = %d]\n", pPars->nMaxSuppSize );
    Abc_Print( -2, "\t-D <num> : the max distance in terms of LUTs (0 < num) [default = %d]\n", pPars->nMaxDistance );
    Abc_Print( -2, "\t-L <num> : the max difference in levels (0 <= num) [default = %d]\n", pPars->nMaxLevelDiff );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to stop traversal (0 < num) [default = %d]\n", pPars->nMaxFanout );
    Abc_Print( -2, "\t-s       : toggle the use of nodes without support overlap [default = %s]\n", pPars->fUseDiffSupp? "yes" : "no" );
    Abc_Print( -2, "\t-c       : toggle the use of TFI/TFO nodes as candidates [default = %s]\n", pPars->fUseTfiTfo? "yes" : "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestDec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_DecTest( char * pFileName, int DecType, int nVarNum, int fVerbose );
    char * pFileName;
    int c;
    int fVerbose = 0;
    int DecType = 0;
    int nVarNum = -1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ANvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            DecType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DecType < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVarNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVarNum < 0 )
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
        Abc_Print( 1,"Input file is not given.\n" );
        return 0;
    }
    if ( nVarNum >= 0 && nVarNum < 6 )
    {
        Abc_Print( 1,"The number of variables cannot be less than 6.\n" );
        return 0;
    }
    // get the output file name
    pFileName = argv[globalUtilOptind];
    // call the testbench
    Abc_DecTest( pFileName, DecType, nVarNum, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: testdec [-AN <num>] [-vh] <file>\n" );
    Abc_Print( -2, "\t           testbench for Boolean decomposition algorithms\n" );
    Abc_Print( -2, "\t-A <num> : decomposition algorithm [default = %d]\n", DecType );
    Abc_Print( -2, "\t               0: none (reading and writing the file)\n" );
    Abc_Print( -2, "\t               1: algebraic factoring applied to ISOP\n" );
    Abc_Print( -2, "\t               2: bi-decomposition with cofactoring\n" );
    Abc_Print( -2, "\t               3: disjoint-support decomposition with cofactoring\n" );
    Abc_Print( -2, "\t               4: updated disjoint-support decomposition with cofactoring\n" );
    Abc_Print( -2, "\t               5: enumerating decomposable variable sets\n" );
    Abc_Print( -2, "\t               6: disjoint-support decomposition with cofactoring and boolean difference analysis\n" );
    Abc_Print( -2, "\t                  from V. Callegaro, F. S. Marranghello, M. G. A. Martins, R. P. Ribas and A. I. Reis,\n");
    Abc_Print( -2, "\t                  \"Bottom-up disjoint-support decomposition based on cofactor and boolean difference analysis,\" ICCD'15.\n" );
    Abc_Print( -2, "\t-N <num> : the number of support variables (binary files only) [default = unused]\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file>   : a text file with truth tables in hexadecimal, listed one per line,\n");
    Abc_Print( -2, "\t           or a binary file with an array of truth tables (in this case,\n");
    Abc_Print( -2, "\t           -N <num> is required to determine how many functions are stored)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestNpn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NpnTest( char * pFileName, int NpnType, int nVarNum, int fDumpRes, int fBinary, int fVerbose );
    char * pFileName;
    int c;
    int fVerbose = 0;
    int NpnType = 0;
    int nVarNum = -1;
    int fDumpRes = 0;
    int fBinary = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ANdbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            NpnType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( NpnType < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVarNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVarNum < 0 )
                goto usage;
            break;
        case 'd':
            fDumpRes ^= 1;
            break;
        case 'b':
            fBinary ^= 1;
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
    if ( nVarNum >= 0 && nVarNum < 6 )
    {
        Abc_Print( 1,"The number of variables cannot be less than 6.\n" );
        return 0;
    }
    // get the output file name
    pFileName = argv[globalUtilOptind];
    // call the testbench
    Abc_NpnTest( pFileName, NpnType, nVarNum, fDumpRes, fBinary, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: testnpn [-AN <num>] [-dbvh] <file>\n" );
    Abc_Print( -2, "\t           testbench for computing (semi-)canonical forms\n" );
    Abc_Print( -2, "\t           of completely-specified Boolean functions up to 16 variables\n" );
    Abc_Print( -2, "\t-A <num> : semi-caninical form computation algorithm [default = %d]\n", NpnType );
    Abc_Print( -2, "\t               0: uniqifying truth tables\n" );
    Abc_Print( -2, "\t               1: exact NPN canonical form by brute-force enumeration\n" );
    Abc_Print( -2, "\t               2: semi-canonical form by counting 1s in cofactors\n" );
    Abc_Print( -2, "\t               3: Jake's hybrid semi-canonical form (fast)\n" );
    Abc_Print( -2, "\t               4: Jake's hybrid semi-canonical form (high-effort)\n" );
    Abc_Print( -2, "\t               5: new fast hybrid semi-canonical form\n" );
    Abc_Print( -2, "\t               6: new phase canonical form\n" );
    Abc_Print( -2, "\t               7: new hierarchical matching\n" );
    Abc_Print( -2, "\t               8: hierarchical matching            by XueGong Zhou at Fudan University, Shanghai\n" );
    Abc_Print( -2, "\t               9: adjustable algorithm (heuristic) by XueGong Zhou at Fudan University, Shanghai\n" );
    Abc_Print( -2, "\t              10: adjustable algorithm (exact)     by XueGong Zhou at Fudan University, Shanghai\n" );
    Abc_Print( -2, "\t              11: new cost-aware exact algorithm   by XueGong Zhou at Fudan University, Shanghai\n" );
    Abc_Print( -2, "\t              12: new fast hybrid semi-canonical form (permutation only)\n" );
    Abc_Print( -2, "\t-N <num> : the number of support variables (binary files only) [default = unused]\n" );
    Abc_Print( -2, "\t-d       : toggle dumping resulting functions into a file [default = %s]\n", fDumpRes? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggle dumping in binary format [default = %s]\n", fBinary? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file>   : a text file with truth tables in hexadecimal, listed one per line,\n");
    Abc_Print( -2, "\t           or a binary file with an array of truth tables (in this case,\n");
    Abc_Print( -2, "\t           -N <num> is required to determine how many functions are stored)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestRPO(Abc_Frame_t * pAbc, int argc, char ** argv) {
    extern int Abc_RpoTest(char * pFileName, int nVarNum, int nThreshold, int fVerbose);
    char * pFileName;
    int c;
    int nVarNum = -1;
    int fVerbose = 0;
    int nThreshold = -1;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "TNvh")) != EOF) {
        switch (c) {
            case 'N':
                if (globalUtilOptind >= argc) {
                    Abc_Print(-1, "Command line switch \"-N\" should be followed by an integer.\n");
                    goto usage;
                }
                nVarNum = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if (nVarNum < 0)
                    goto usage;
                break;
            case 'T':
                if (globalUtilOptind >= argc) {
                    Abc_Print(-1, "Command line switch \"-T\" should be followed by an integer.\n");
                    goto usage;
                }
                nThreshold = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if (nThreshold < 0)
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
    if (argc != globalUtilOptind + 1)
    {
        Abc_Print(1, "Input file is not given.\n");
        goto usage;
    }
    // get the output file name
    pFileName = argv[globalUtilOptind];
    // call the testbench
    Abc_RpoTest( pFileName, nVarNum, nThreshold, fVerbose );
    return 0;

usage:
    Abc_Print(-2, "usage: testrpo [-NT <num>] [-vh] <file>\n");
    Abc_Print(-2, "\t           RPO algorithm developed and implemented by Mayler G. A. Martins,\n");
    Abc_Print(-2, "\t           Vinicius Callegaro, Renato P. Ribas and Andre' I. Reis\n");
    Abc_Print(-2, "\t           at Federal University of Rio Grande do Sul, Porto Alegre, Brazil\n");
    Abc_Print(-2, "\t-N <num> : the number of support variables (binary files only) [default = unused]\n");
    Abc_Print(-2, "\t-T <num> : the number of recursions accepted before abort [default = INFINITE]\n");
    Abc_Print(-2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no");
    Abc_Print(-2, "\t-h       : print the command usage\n");
    Abc_Print(-2, "\t<file>   : a text file with truth tables in hexadecimal, listed one per line,\n");
    Abc_Print(-2, "\t           or a binary file with an array of truth tables (in this case,\n");
    Abc_Print(-2, "\t           -N <num> is required to determine how many functions are stored)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestTruth( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int * Kit_TruthTest( char * pFileName );
    int * pResult = NULL;
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
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 1,"Input file is not given.\n" );
        return 0;
    }
    pResult = Kit_TruthTest( argv[globalUtilOptind] );
    ABC_FREE( pResult );
    return 0;

usage:
    Abc_Print( -2, "usage: testtruth [-vh] <file>\n" );
    Abc_Print( -2, "\t           printing truth table stats\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestSupp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkSuppMinFile( char * pFileName );
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
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 1,"Input file is not given.\n" );
        return 0;
    }
    Abc_NtkSuppMinFile( argv[globalUtilOptind] );
    return 0;

usage:
    Abc_Print( -2, "usage: testsupp [-vh] <file>\n" );
    Abc_Print( -2, "\t           reads truth tables from file and support-minimizes them\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file>   : file to read the truth tables from\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExtract( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkShareXor( Abc_Ntk_t * pNtk, int nMultiSize, int fAnd, int fVerbose );
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMultiSize, fAnd, fVerbose;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nMultiSize = 3;
    fAnd       = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nMultiSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMultiSize < 0 )
                goto usage;
            break;
        case 'a':
            fAnd ^= 1;
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
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }
    // get the new network
    pNtkRes = Abc_NtkShareXor( pNtk, nMultiSize, fAnd, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Cascade synthesis has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: extract [-K <num>] [-avh]\n" );
    Abc_Print( -2, "\t           extracts shared logic from multi-input gates\n" );
    Abc_Print( -2, "\t-K <num> : the minimum gate size to consider for extraction [default = %d]\n", nMultiSize );
    Abc_Print( -2, "\t-a       : toggle multi-input XOR vs multi-input AND [default = %s]\n", fAnd? "AND": "XOR" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandVarMin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_SuppTest( int nOnes, int nVars, int fUseSimple, int fCheck, int fVerbose );
    extern void Abc_SuppReadMinTest( char * pFileName );
    int nOnes      =  4;
    int nVars      = 20;
    int fUseSimple =  0;
    int fCheck     =  0;
    int fVerbose   =  0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MNocvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nOnes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOnes < 0 )
                goto usage;
            break;
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
        case 'o':
            fUseSimple ^= 1;
            break;
        case 'c':
            fCheck ^= 1;
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
    // get the file name
    if ( argc == globalUtilOptind + 1 )
    {
        Abc_SuppReadMinTest( argv[globalUtilOptind] );
        return 0;
    }
    Abc_SuppTest( nOnes, nVars, fUseSimple, fCheck, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: varmin [-MN <num>] [-ocvh]\n" );
    Abc_Print( -2, "\t           performs support minimization\n" );
    Abc_Print( -2, "\t-M <num> : the number of ones in the combination [default = %d]\n", nOnes );
    Abc_Print( -2, "\t-N <num> : the number of variables in the problem [default = %d]\n", nVars );
    Abc_Print( -2, "\t-o       : toggle computing reduced difference matrix [default = %s]\n", fUseSimple? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle verifying the final result [default = %s]\n", fCheck? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandReorder( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fVerbose = 0;
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "Variable reordering is possible when node functions are BDDs (run \"bdd\").\n" );
        return 1;
    }
    Abc_NtkBddReorder( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: reorder [-vh]\n" );
    Abc_Print( -2, "\t         reorders local functions of the nodes using sifting\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBidec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fVerbose = 0;
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsAigLogic(pNtk) )
    {
        Abc_Print( -1, "Bi-decomposition only works when node functions are AIGs (run \"aig\").\n" );
        return 1;
    }
    Abc_NtkBidecResyn( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: bidec [-vh]\n" );
    Abc_Print( -2, "\t         applies bi-decomposition to local functions of the nodes\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMuxes( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fGlobal = 0, fUseAdd = 0, Limit = 1000000;
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Bgah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            Limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Limit < 0 )
                goto usage;
            break;
        case 'g':
            fGlobal ^= 1;
            break;
        case 'a':
            fUseAdd ^= 1;
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

    if ( fGlobal )
    {
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "The current network should be an AIG.\n" );
            return 1;
        }
    }
    else
    {
        if ( !Abc_NtkIsBddLogic(pNtk) )
        {
            Abc_Print( -1, "Only a BDD logic network can be converted to MUXes.\n" );
            return 1;
        }
    }

    // get the new network
    pNtkRes = Abc_NtkBddToMuxes( pNtk, fGlobal, Limit, fUseAdd );
    if ( pNtkRes == NULL )
    {
        Abc_Print( 0, "Converting to MUXes has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: muxes [-B num] [-gah]\n" );
    Abc_Print( -2, "\t          converts the current network into a network derived by\n" );
    Abc_Print( -2, "\t          replacing all nodes by DAGs isomorphic to the local BDDs\n" );
    Abc_Print( -2, "\t-B <num>: limit on live BDD nodes during collapsing [default = %d]\n", Limit );
    Abc_Print( -2, "\t-g      : toggle visualizing the global BDDs of primary outputs [default = %s].\n", fGlobal? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggle using ADDs instead of BDDs [default = %s].\n", fUseAdd? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCubes( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkSopToCubes( Abc_Ntk_t * pNtk, int fXor );
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fXor = 0;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "xh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'x':
            fXor ^= 1;
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

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only a SOP logic network can be transformed into cubes.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkSopToCubes( pNtk, fXor );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to cubes has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cubes [-xh]\n" );
    Abc_Print( -2, "\t        converts the current network into a network derived by creating\n" );
    Abc_Print( -2, "\t        a separate node for each product and sum in the local SOPs\n" );
    Abc_Print( -2, "\t-x    : toggle using XOR instead of OR [default = %s]\n", fXor? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExpand( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkExpandCubes( Abc_Ntk_t * pNtk, Gia_Man_t * pGia, int fVerbose );
    Abc_Ntk_t * pStrash, * pNtk2, * pNtk = Abc_FrameReadNtk(pAbc);
    Gia_Man_t * pGia; int c, fVerbose = 0;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only a SOP logic network can be transformed into cubes.\n" );
        return 1;
    }
    if ( Abc_NtkLevel(pNtk) > 1 )
    {
        Abc_Print( -1, "The number of logic levels is more than 1 (collapse the network and try again).\n" );
        return 1;
    }
    // read the offset representation
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 0, "Using the complement of the current network as its offset.\n" );
        pNtk2 = Abc_NtkDup( pNtk );
    }
    else
    {
        char * FileName = argv[globalUtilOptind];
        pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
        if ( pNtk2 == NULL )
        {
            Abc_Print( -1, "Failed to read the current network from file \"%s\".\n", FileName );
            return 1;
        }
    }
    // strash the network
    pStrash = Abc_NtkStrash( pNtk2, 0, 1, 0 );
    Abc_NtkDelete( pNtk2 );
    // convert it into an AIG
    pGia = Abc_NtkClpGia( pStrash );
    //Gia_AigerWrite( pGia, "aig_dump.aig", 0, 0, 0 );
    Abc_NtkDelete( pStrash );
    // get the new network
    Abc_NtkExpandCubes( pNtk, pGia, fVerbose );
    Gia_ManStop( pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: expand [-vh] <file>\n" );
    Abc_Print( -2, "\t        expands cubes against the offset\n" );
    Abc_Print( -2, "\t-v    : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tfile  : (optional) representation of on-set plus dc-set\n");

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSplitSop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkSplitSop( Abc_Ntk_t * pNtk, int nCubesMax, int fVerbose );
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fVerbose = 0, nCubesMax = 100;
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubesMax < 0 )
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only a SOP logic network can be transformed into cubes.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkSplitSop( pNtk, nCubesMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to cubes has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: splitsop [-N num] [-vh]\n" );
    Abc_Print( -2, "\t         splits nodes whose SOP size is larger than the given one\n" );
    Abc_Print( -2, "\t-N num : the maximum number of cubes after splitting [default = %d]\n", nCubesMax );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cut_Params_t Params, * pParams = &Params;
    Cut_Man_t * pCutMan;
    Cut_Oracle_t * pCutOracle = NULL;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fOracle;
    extern Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );
    extern void Abc_NtkCutsOracle( Abc_Ntk_t * pNtk, Cut_Oracle_t * pCutOracle );

    // set defaults
    fOracle = 0;
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax    = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax    = 1000;  // the max number of cuts kept at a node
    pParams->fTruth      = 1;     // compute truth tables
    pParams->fFilter     = 1;     // filter dominated cuts
    pParams->fDrop       = 0;     // drop cuts on the fly
    pParams->fDag        = 1;     // compute DAG cuts
    pParams->fTree       = 0;     // compute tree cuts
    pParams->fGlobal     = 0;     // compute global cuts
    pParams->fLocal      = 0;     // compute local cuts
    pParams->fFancy      = 0;     // compute something fancy
    pParams->fRecordAig  = 1;     // compute something fancy
    pParams->fMap        = 0;     // compute mapping delay
    pParams->fAdjust     = 0;     // removes useless fanouts
    pParams->fNpnSave    = 0;     // enables dumping truth tables
    pParams->fVerbose    = 0;     // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMtfdxyglzamjvosh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nVarsMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nKeepMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nKeepMax < 0 )
                goto usage;
            break;
        case 't':
            pParams->fTruth ^= 1;
            break;
        case 'f':
            pParams->fFilter ^= 1;
            break;
        case 'd':
            pParams->fDrop ^= 1;
            break;
        case 'x':
            pParams->fDag ^= 1;
            break;
        case 'y':
            pParams->fTree ^= 1;
            break;
        case 'g':
            pParams->fGlobal ^= 1;
            break;
        case 'l':
            pParams->fLocal ^= 1;
            break;
        case 'z':
            pParams->fFancy ^= 1;
            break;
        case 'a':
            pParams->fRecordAig ^= 1;
            break;
        case 'm':
            pParams->fMap ^= 1;
            break;
        case 'j':
            pParams->fAdjust ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'o':
            fOracle ^= 1;
            break;
        case 's':
            pParams->fNpnSave ^= 1;
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
        Abc_Print( -1, "Cut computation is available only for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }
    if ( pParams->fDag && pParams->fTree )
    {
        Abc_Print( -1, "Cannot compute both DAG cuts and tree cuts at the same time.\n" );
        return 1;
    }

    if ( pParams->fNpnSave )
    {
        pParams->nVarsMax = 6;
        pParams->fTruth = 1;
    }

    if ( fOracle )
        pParams->fRecord = 1;
    pCutMan = Abc_NtkCuts( pNtk, pParams );
    if ( fOracle )
        pCutOracle = Cut_OracleStart( pCutMan );
    Cut_ManStop( pCutMan );
    if ( fOracle )
    {
        assert(pCutOracle);
        Abc_NtkCutsOracle( pNtk, pCutOracle );
        Cut_OracleStop( pCutOracle );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: cut [-K num] [-M num] [-tfdcovamjsvh]\n" );
    Abc_Print( -2, "\t         computes k-feasible cuts for the AIG\n" );
    Abc_Print( -2, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",     CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    Abc_Print( -2, "\t-M num : max number of cuts stored at a node [default = %d]\n",        pParams->nKeepMax );
    Abc_Print( -2, "\t-t     : toggle truth table computation [default = %s]\n",             pParams->fTruth?   "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle filtering of duplicated/dominated [default = %s]\n",   pParams->fFilter?  "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dropping when fanouts are done [default = %s]\n",      pParams->fDrop?    "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle computing only DAG cuts [default = %s]\n",             pParams->fDag?     "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle computing only tree cuts [default = %s]\n",            pParams->fTree?    "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle computing only global cuts [default = %s]\n",          pParams->fGlobal?  "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle computing only local cuts [default = %s]\n",           pParams->fLocal?   "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle fancy computations [default = %s]\n",                  pParams->fFancy?   "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle recording cut functions [default = %s]\n",             pParams->fRecordAig?"yes": "no" );
    Abc_Print( -2, "\t-m     : toggle delay-oriented FPGA mapping [default = %s]\n",         pParams->fMap?     "yes": "no" );
    Abc_Print( -2, "\t-j     : toggle removing fanouts due to XOR/MUX [default = %s]\n",     pParams->fAdjust?  "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle creating library of 6-var functions [default = %s]\n", pParams->fNpnSave?  "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",        pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEspresso( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkEspresso( Abc_Ntk_t * pNtk, int fVerbose );

    if ( argc == 2 && !strcmp(argv[1], "-h") )
    {
        Abc_Print( -2, "The espresso command is currently disabled.\n" );
        return 1;
    }

    Abc_Print( -1, "This command is currently disabled.\n" );
    return 0;

    // set defaults
    fVerbose = 0;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "SOP minimization is possible for logic networks (run \"renode\").\n" );
        return 1;
    }
//    Abc_NtkEspresso( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: espresso [-vh]\n" );
    Abc_Print( -2, "\t         minimizes SOPs of the local functions using Espresso\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCover( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;
    int fUseSop;
    int fUseEsop;
    int fUseInvs;
    int nFaninMax;
    int nCubesMax;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fUseSop   =  1;
    fUseEsop  =  0;
    fVerbose  =  0;
    fUseInvs  =  1;
    nFaninMax =  8;
    nCubesMax =  8;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IPsxivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFaninMax < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubesMax < 0 )
                goto usage;
            break;
        case 's':
            fUseSop ^= 1;
            break;
        case 'x':
            fUseEsop ^= 1;
            break;
        case 'i':
            fUseInvs ^= 1;
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

    // run the command
    pNtkRes = Abc_NtkSopEsopCover( pNtk, nFaninMax, nCubesMax, fUseEsop, fUseSop, fUseInvs, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cover [-IP num] [-sxvh]\n" );
    Abc_Print( -2, "\t         decomposition into a network of SOP/ESOP PLAs\n" );
    Abc_Print( -2, "\t         (this command is known to have bugs)\n");
    Abc_Print( -2, "\t-I num : maximum number of inputs [default = %d]\n", nFaninMax );
    Abc_Print( -2, "\t-P num : maximum number of products [default = %d]\n", nCubesMax );
    Abc_Print( -2, "\t-s     : toggle the use of SOPs [default = %s]\n", fUseSop? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle the use of ESOPs [default = %s]\n", fUseEsop? "yes": "no" );
//    Abc_Print( -2, "\t-i     : toggle the use of interters [default = %s]\n", fUseInvs? "yes": "no" );
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
int Abc_CommandInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes = NULL;
    char ** pArgvNew;
    int nArgcNew;
    int c, fDelete1, fDelete2;
    int fRelation;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkInter( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fRelation, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRelation = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fRelation ^= 1;
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
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 1;
    if ( nArgcNew == 0 )
    {
        Abc_Obj_t * pObj;
        int i;
        Abc_Print( -1, "Deriving new circuit structure for the current network.\n" );
        Abc_NtkForEachPo( pNtk2, pObj, i )
            Abc_ObjXorFaninC( pObj, 0 );
    }
    if ( fRelation && Abc_NtkCoNum(pNtk1) != 1 )
    {
        Abc_Print( -1, "Computation of interplants as a relation only works for single-output functions.\n" );
        Abc_Print( -1, "Use command \"cone\" to extract one output cone from the multi-output network.\n" );
    }
    else
        pNtkRes = Abc_NtkInter( pNtk1, pNtk2, fRelation, fVerbose );
    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );

    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: inter [-rvh] <onset.blif> <offset.blif>\n" );
    Abc_Print( -2, "\t         derives interpolant of two networks representing onset and offset;\n" );
    Abc_Print( -2, "\t-r     : toggle computing interpolant as a relation [default = %s]\n", fRelation? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t         \n" );
    Abc_Print( -2, "\t         Comments:\n" );
    Abc_Print( -2, "\t         \n" );
    Abc_Print( -2, "\t         The networks given on the command line should have the same CIs/COs.\n" );
    Abc_Print( -2, "\t         If only one network is given on the command line, this network\n" );
    Abc_Print( -2, "\t         is assumed to be the offset, while the current network is the onset.\n" );
    Abc_Print( -2, "\t         If no network is given on the command line, the current network is\n" );
    Abc_Print( -2, "\t         assumed to be the onset and its complement is taken to be the offset.\n" );
    Abc_Print( -2, "\t         The resulting interpolant is stored as the current network.\n" );
    Abc_Print( -2, "\t         To verify that the interpolant agrees with the onset and the offset,\n" );
    Abc_Print( -2, "\t         save it in file \"inter.blif\" and run the following:\n" );
    Abc_Print( -2, "\t         (a) \"miter -i <onset.blif> <inter.blif>; iprove\"\n" );
    Abc_Print( -2, "\t         (b) \"miter -i <inter.blif> <offset_inv.blif>; iprove\"\n" );
    Abc_Print( -2, "\t         where <offset_inv.blif> is the network derived by complementing the\n" );
    Abc_Print( -2, "\t         outputs of <offset.blif>: \"r <offset.blif>; st -i; w <offset_inv.blif>\"\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQuaVar( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, iVar, fUniv, fVerbose, RetValue;
    extern int Abc_NtkQuantify( Abc_Ntk_t * pNtk, int fUniv, int iVar, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    iVar = 0;
    fUniv = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Iuvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 )
                goto usage;
            break;
        case 'u':
            fUniv ^= 1;
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
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }

    // get the strashed network
    pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
    RetValue = Abc_NtkQuantify( pNtkRes, fUniv, iVar, fVerbose );
    // clean temporary storage for the cofactors
    Abc_NtkCleanData( pNtkRes );
    Abc_AigCleanup( (Abc_Aig_t *)pNtkRes->pManFunc );
    // check the result
    if ( !RetValue )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qvar [-I num] [-uvh]\n" );
    Abc_Print( -2, "\t         quantifies one variable using the AIG\n" );
    Abc_Print( -2, "\t-I num : the zero-based index of a variable to quantify [default = %d]\n", iVar );
    Abc_Print( -2, "\t-u     : toggle universal quantification [default = %s]\n", fUniv? "yes": "no" );
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
int Abc_CommandQuaRel( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, iVar, fInputs, fVerbose;
    extern Abc_Ntk_t * Abc_NtkTransRel( Abc_Ntk_t * pNtk, int fInputs, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    iVar = 0;
    fInputs = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Iqvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 )
                goto usage;
            break;
        case 'q':
            fInputs ^= 1;
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
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for sequential circuits.\n" );
        return 1;
    }

    // get the strashed network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 1, 0 );
        pNtkRes = Abc_NtkTransRel( pNtk, fInputs, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    else
        pNtkRes = Abc_NtkTransRel( pNtk, fInputs, fVerbose );
    // check if the result is available
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qrel [-qvh]\n" );
    Abc_Print( -2, "\t         computes transition relation of the sequential network\n" );
//    Abc_Print( -2, "\t-I num : the zero-based index of a variable to quantify [default = %d]\n", iVar );
    Abc_Print( -2, "\t-q     : perform quantification of inputs [default = %s]\n", fInputs? "yes": "no" );
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
int Abc_CommandSenseInput( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Vec_Int_t * vResult;
    int c, nConfLim, fVerbose;

    extern Vec_Int_t * Abc_NtkSensitivity( Abc_Ntk_t * pNtk, int nConfLim, int fVerbose );
    // set defaults
    nConfLim   = 1000;
    fVerbose   =    1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLim < 0 )
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational transition relations.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) < 2 )
    {
        Abc_Print( -1, "The network should have at least two outputs.\n" );
        return 1;
    }

    vResult = Abc_NtkSensitivity( pNtk, nConfLim, fVerbose );
    Vec_IntFree( vResult );
    return 0;

usage:
    Abc_Print( -2, "usage: senseinput [-C num] [-vh]\n" );
    Abc_Print( -2, "\t         computes sensitivity of POs to PIs under constraint\n" );
    Abc_Print( -2, "\t         constraint should be represented as the last PO\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfLim );
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
int Abc_CommandICut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, nInputs;
    extern void Abc_NtkIvyCuts( Abc_Ntk_t * pNtk, int nInputs );

    // set defaults
    nInputs = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nInputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInputs < 0 )
                goto usage;
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
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    Abc_NtkIvyCuts( pNtk, nInputs );
    return 0;

usage:
    Abc_Print( -2, "usage: icut [-K num] [-h]\n" );
    Abc_Print( -2, "\t         computes sequential cuts of the given size\n" );
    Abc_Print( -2, "\t-K num : the number of cut inputs (2 <= num <= 6) [default = %d]\n", nInputs );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNpnLoad( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Npn_ManLoad( char * pFileName );
    char * pFileName;
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
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    pFileName = argv[globalUtilOptind];
    Npn_ManLoad( pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: npnload <filename>\n" );
    Abc_Print( -2, "\t         loads previously saved 6-input function library from file\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNpnSave( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Npn_ManSave( char * pFileName );
    char * pFileName;
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
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    pFileName = argv[globalUtilOptind];
    Npn_ManSave( pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: npnsave <filename>\n" );
    Abc_Print( -2, "\t         saves current 6-input function library into file\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdSave( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * FileName;
    char ** pArgvNew;
    int nArgcNew;
    int c, fSecond = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fSecond ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    // get the input file name
    FileName = (nArgcNew == 1) ? pArgvNew[0] : NULL;
    if ( fSecond )
    {
        if ( !Abc_FrameReadManDsd2() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 1;
        }
        If_DsdManSave( (If_DsdMan_t *)Abc_FrameReadManDsd2(), FileName );
    }
    else
    {
        if ( !Abc_FrameReadManDsd() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 1;
        }
        If_DsdManSave( (If_DsdMan_t *)Abc_FrameReadManDsd(), FileName );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_save [-bh] <file>\n" );
    Abc_Print( -2, "\t         saves DSD manager into a file\n");
    Abc_Print( -2, "\t-b     : toggles processing second manager [default = %s]\n", fSecond? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : (optional) file name to write\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdLoad( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * FileName, * pTemp;
    char ** pArgvNew;
    int c, nArgcNew, fSecond = 0;
    FILE * pFile;
    If_DsdMan_t * pDsdMan;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fSecond ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    // get the input file name
    FileName = pArgvNew[0];
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
    if ( fSecond )
    {
        Abc_FrameSetManDsd2( NULL );
        pDsdMan = If_DsdManLoad(FileName);
        if ( pDsdMan == NULL )
            return 1;
        Abc_FrameSetManDsd2( pDsdMan );
    }
    else
    {
        Abc_FrameSetManDsd( NULL );
        pDsdMan = If_DsdManLoad(FileName);
        if ( pDsdMan == NULL )
            return 1;
        Abc_FrameSetManDsd( pDsdMan );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_load [-bh] <file>\n" );
    Abc_Print( -2, "\t         loads DSD manager from file\n");
    Abc_Print( -2, "\t-b     : toggles processing second manager [default = %s]\n", fSecond? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name to read\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdFree( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fSecond = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fSecond ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fSecond )
    {
        if ( !Abc_FrameReadManDsd2() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 0;
        }
        Abc_FrameSetManDsd2( NULL );
    }
    else
    {
        if ( !Abc_FrameReadManDsd() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 0;
        }
        Abc_FrameSetManDsd( NULL );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_free [-bh]\n" );
    Abc_Print( -2, "\t         deletes DSD manager\n" );
    Abc_Print( -2, "\t-b     : toggles processing second manager [default = %s]\n", fSecond? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, Number = 0, Support = 0, fOccurs = 0, fTtDump = 0, fSecond = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSotbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a floating point number.\n" );
                goto usage;
            }
            Number = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Number < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a floating point number.\n" );
                goto usage;
            }
            Support = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Support < 0 )
                goto usage;
            break;
        case 'o':
            fOccurs ^= 1;
            break;
        case 't':
            fTtDump ^= 1;
            break;
        case 'b':
            fSecond ^= 1;
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
    if ( fSecond )
    {
        if ( !Abc_FrameReadManDsd2() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 0;
        }
        If_DsdManPrint( (If_DsdMan_t *)Abc_FrameReadManDsd2(), NULL, Number, Support, fOccurs, fTtDump, fVerbose );
    }
    else
    {
        if ( !Abc_FrameReadManDsd() )
        {
            Abc_Print( -1, "The DSD manager is not started.\n" );
            return 0;
        }
        If_DsdManPrint( (If_DsdMan_t *)Abc_FrameReadManDsd(), NULL, Number, Support, fOccurs, fTtDump, fVerbose );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_ps [-NS num] [-obvh]\n" );
    Abc_Print( -2, "\t         prints statistics of the DSD manager\n" );
    Abc_Print( -2, "\t-N num : show structures whose ID divides by N [default = %d]\n",   Number );
    Abc_Print( -2, "\t-S num : show structures whose support size is S [default = %d]\n", Support );
    Abc_Print( -2, "\t-o     : toggles printing occurrence distribution [default = %s]\n", fOccurs? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggles dumping truth tables [default = %s]\n",            fTtDump? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles processing second manager [default = %s]\n",       fSecond? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n",                  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdMatch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pStruct = NULL;
    int c, fVerbose = 0, fFast = 0, fAdd = 0, fSpec = 0, LutSize = 0, nConfls = 10000, nProcs = 1, nInputs = 0;
    If_DsdMan_t * pDsdMan = (If_DsdMan_t *)Abc_FrameReadManDsd();
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCPISfasvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a floating point number.\n" );
                goto usage;
            }
            LutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LutSize < 4 || LutSize > 6 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a floating point number.\n" );
                goto usage;
            }
            nConfls = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a floating point number.\n" );
                goto usage;
            }
            nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a floating point number.\n" );
                goto usage;
            }
            nInputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by string.\n" );
                goto usage;
            }
            pStruct = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'f':
            fFast ^= 1;
            break;
        case 'a':
            fAdd ^= 1;
            break;
        case 's':
            fSpec ^= 1;
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
    if ( !Abc_FrameReadManDsd() )
    {
        Abc_Print( -1, "The DSD manager is not started.\n" );
        return 0;
    }
    if ( pStruct )
    {
        char * pStructCur = If_DsdManGetCellStr( pDsdMan );
        if ( pStructCur && strcmp(pStructCur, pStruct) )
        {
            Abc_Print( -1, "DSD manager matched with cell %s should be cleaned by \"dsd_filter -m\" before matching with cell %s.\n", pStructCur, pStruct );
            return 0;
        }
        Id_DsdManTuneStr( pDsdMan, pStruct, nConfls, nProcs, nInputs, fVerbose );
    }
    else
        If_DsdManTune( pDsdMan, LutSize, fFast, fAdd, fSpec, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_match [-KCPI num] [-fasvh] [-S str]\n" );
    Abc_Print( -2, "\t         matches DSD structures with the given cell\n" );
    Abc_Print( -2, "\t-K num : LUT size used for tuning [default = %d]\n",        LutSize );
    Abc_Print( -2, "\t-C num : the maximum number of conflicts [default = %d]\n", nConfls );
    Abc_Print( -2, "\t-P num : the maximum number of processes [default = %d]\n", nProcs );
    Abc_Print( -2, "\t-I num : skip checking if support is less than this [default = %d]\n", nInputs );
    Abc_Print( -2, "\t-f     : toggles using fast check [default = %s]\n",        fFast? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggles adding tuning to the current one [default = %s]\n",    fAdd? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles using specialized check [default = %s]\n", fSpec? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n",          fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-S str : string representing programmable cell [default = %s]\n", pStruct ? pStruct : "not used" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * FileName, * pTemp;
    char ** pArgvNew;
    int c, nArgcNew;
    FILE * pFile;
    If_DsdMan_t * pDsdMan;
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
    if ( !Abc_FrameReadManDsd() )
    {
        Abc_Print( -1, "The DSD manager is not started.\n" );
        return 0;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    // get the input file name
    FileName = pArgvNew[0];
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
    pDsdMan = If_DsdManLoad(FileName);
    if ( pDsdMan == NULL )
        return 1;
    If_DsdManMerge( (If_DsdMan_t *)Abc_FrameReadManDsd(), pDsdMan );
    If_DsdManFree( pDsdMan, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_merge [-h] <file>\n" );
    Abc_Print( -2, "\t         merges DSD manager from file with the current one\n");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name to read\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDsdFilter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    If_DsdMan_t * pDsd = (If_DsdMan_t *)Abc_FrameReadManDsd();
    int c, nLimit = 0, nLutSize = -1, fCleanOccur = 0, fCleanMarks = 0, fInvMarks = 0, fUnate = 0, fThresh = 0, fThreshHeuristic = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LKomiutsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a floating point number.\n" );
                goto usage;
            }
            nLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a floating point number.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'o':
            fCleanOccur ^= 1;
            break;
        case 'm':
            fCleanMarks ^= 1;
            break;
        case 'i':
            fInvMarks ^= 1;
            break;
        case 'u':
            fUnate ^= 1;
            break;
        case 't':
            fThresh ^= 1;
            break;
        case 's':
            fThreshHeuristic ^= 1;
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
    if ( pDsd == NULL )
    {
        Abc_Print( -1, "The DSD manager is not started.\n" );
        return 0;
    }
    if ( nLimit > 0 )
        Abc_FrameSetManDsd( If_DsdManFilter(pDsd, nLimit) );
    if ( nLutSize >= 0 )
        If_DsdManSetLutSize( pDsd, nLutSize );
    if ( fCleanOccur )
        If_DsdManCleanOccur( pDsd, fVerbose );
    if ( fCleanMarks )
        If_DsdManCleanMarks( pDsd, fVerbose );
    if ( fInvMarks )
        If_DsdManInvertMarks( pDsd, fVerbose );
#ifdef ABC_USE_CUDD
    else if ( nLimit == 0 )
        Id_DsdManTuneThresh( pDsd, fUnate, fThresh, fThreshHeuristic, fVerbose );
#endif
    return 0;

usage:
    Abc_Print( -2, "usage: dsd_filter [-LK num] [-omiutsvh]\n" );
    Abc_Print( -2, "\t         filtering structured and modifying parameters of DSD manager\n" );
    Abc_Print( -2, "\t-L num : remove structures with fewer occurrences that this [default = %d]\n", nLimit );
    Abc_Print( -2, "\t-K num : new LUT size to set for the DSD manager [default = %d]\n",           nLutSize );
    Abc_Print( -2, "\t-o     : toggles cleaning occurrence counters [default = %s]\n",              fCleanOccur? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles cleaning matching marks [default = %s]\n",                   fCleanMarks? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggles inverting matching marks [default = %s]\n",                  fInvMarks? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggles marking unate functions [default = %s]\n",                   fUnate? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggles marking threshold functions [default = %s]\n",               fThresh? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles marking threshold functions heuristically [default = %s]\n", fThreshHeuristic?"yes":"no");
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n",                            fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t        \n" );
    Abc_Print( -2, "\t         Option \"dsd_filter -s\" was contributed by Augusto Neutzling and Jody Matos from\n" );
    Abc_Print( -2, "\t         Federal University of Rio Grande do Sul, Brazil. The paper describing the method:\n" );
    Abc_Print( -2, "\t         A. Neutzling, J. M. Matos, A. Mishchenko, R. Ribas, and A. Reis,\n" );
    Abc_Print( -2, "\t         \"Threshold logic synthesis based on cut pruning\". Proc. ICCAD 2015.\n" );
//    Abc_Print( -2, "\t        http://www.eecs.berkeley.edu/~alanmi/publications/2015/iccad15_thresh.pdf\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dsd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCollapseTest( Gia_Man_t * p, int fVerbose );
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fUpdateLevel = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Dsd(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManCollapseTest( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dsd [-vh]\n" );
    Abc_Print( -2, "\t         performs DSD-based collapsing\n" );
//    Abc_Print( -2, "\t-l     : toggle level update during rewriting [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandAbc9Bidec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fUpdateLevel = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Bidec(): There is no AIG.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bidec(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pTemp = Gia_ManPerformBidec( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &bidec [-vh]\n" );
    Abc_Print( -2, "\t         performs heavy rewriting of the AIG\n" );
//    Abc_Print( -2, "\t-l     : toggle level update during rewriting [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandAbc9Fx( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int nNewNodesMax = 1000000;
    int LitCountMax  =       0;
    int fReverse     =       0;
    int c, fVerbose  =       0;
    int fVeryVerbose =       0;
    // set the defaults
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NMrvwh")) != EOF )
    {
        switch (c)
        {
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                nNewNodesMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nNewNodesMax < 0 )
                    goto usage;
                break;
            case 'M':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                    goto usage;
                }
                LitCountMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( LitCountMax < 0 )
                    goto usage;
                break;
            case 'r':
                fReverse ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'w':
                fVeryVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): There is no AIG.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pTemp = Gia_ManPerformFx( pAbc->pGia, nNewNodesMax, LitCountMax, fReverse, fVerbose, fVeryVerbose );
    if ( pTemp != NULL )
        Abc_FrameUpdateGia( pAbc, pTemp );
    else
        Abc_Print( -1, "Abc_CommandAbc9Fx(): Command has failed.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: &fx [-NM <num>] [-vh]\n");
    Abc_Print( -2, "\t           extract shared logic using the classical \"fast_extract\" algorithm\n");
    Abc_Print( -2, "\t-N <num> : max number of divisors to extract during this run [default = %d]\n", nNewNodesMax );
    Abc_Print( -2, "\t-M <num> : upper bound on literal count of divisors to extract [default = %d]\n", LitCountMax );
    Abc_Print( -2, "\t-r       : reversing variable order during ISOP computation [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Extract( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Abc_NtkShareXorGia( Gia_Man_t * p, int nMultiSize, int fAnd, int fVerbose );
    Gia_Man_t * pTemp;
    int nMultiSize = 3;
    int c, fAnds = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Kavh")) != EOF )
    {
        switch (c)
        {
            case 'K':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                    goto usage;
                }
                nMultiSize = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nMultiSize < 0 )
                    goto usage;
                break;
            case 'a':
                fAnds ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Abc_NtkShareXorGia( pAbc->pGia, nMultiSize, fAnds, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &extract [-K <num>] [-vh]\n");
    Abc_Print( -2, "\t           extract shared logic for XOR-rich circuits\n");
    Abc_Print( -2, "\t-K <num> : the minimum gate size to consider for extraction [default = %d]\n", nMultiSize );
    Abc_Print( -2, "\t-a       : toogle extracting ANDs instead of XORs [default = %s]\n", fAnds? "yes": "no" );
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sopb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int nLevelMax   = 0;
    int nTimeWindow = 0;
    int nCutNum     = 8;
    int nRelaxRatio = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LWCRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelMax < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeWindow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeWindow < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRelaxRatio < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Sopb(): There is no AIG.\n" );
        return 1;
    }
    if ( nLevelMax || nTimeWindow )
        pTemp = Gia_ManPerformSopBalanceWin( pAbc->pGia, nLevelMax, nTimeWindow, nCutNum, nRelaxRatio, fVerbose );
    else
        pTemp = Gia_ManPerformSopBalance( pAbc->pGia, nCutNum, nRelaxRatio, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &sopb [-LWCR num] [-vh]\n" );
    Abc_Print( -2, "\t         performs SOP balancing\n" );
    Abc_Print( -2, "\t-L num : optimize paths above this level [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-W num : optimize paths falling into this window [default = %d]\n", nTimeWindow );
    Abc_Print( -2, "\t-C num : the number of cuts at a node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-R num : the delay relaxation ratio (num >= 0) [default = %d]\n", nRelaxRatio );
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
int Abc_CommandAbc9Dsdb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int nLevelMax   = 0;
    int nTimeWindow = 0;
    int nLutSize    = 6;
    int nCutNum     = 8;
    int nRelaxRatio = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LWKCRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelMax < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeWindow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeWindow < 0 )
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
         case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRelaxRatio < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Dsdb(): There is no AIG.\n" );
        return 1;
    }
    if ( nLutSize > DAU_MAX_VAR )
    {
        printf( "Abc_CommandAbc9Dsdb(): Size of the required DSD manager (%d) exceeds the precompiled limit (%d) (change parameter DAU_MAX_VAR).\n", nLutSize, DAU_MAX_VAR );
        return 0;
    }
    if ( Abc_FrameReadManDsd2() && nLutSize > If_DsdManVarNum((If_DsdMan_t*)Abc_FrameReadManDsd2()) )
    {
        printf( "Abc_CommandAbc9Dsdb(): Incompatible size of the DSD manager (run \"dsd_free -b\").\n" );
        return 0;
    }
    if ( nLevelMax || nTimeWindow )
        pTemp = Gia_ManPerformDsdBalanceWin( pAbc->pGia, nLevelMax, nTimeWindow, nLutSize, nCutNum, nRelaxRatio, fVerbose );
    else
        pTemp = Gia_ManPerformDsdBalance( pAbc->pGia, nLutSize, nCutNum, nRelaxRatio, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dsdb [-LWKCR num] [-vh]\n" );
    Abc_Print( -2, "\t         performs DSD balancing\n" );
    Abc_Print( -2, "\t-L num : optimize paths above this level [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-W num : optimize paths falling into this window [default = %d]\n", nTimeWindow );
    Abc_Print( -2, "\t-K num : the number of LUT inputs (LUT size) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-C num : the number of cuts at a node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-R num : the delay relaxation ratio (num >= 0) [default = %d]\n", nRelaxRatio );
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
int Abc_CommandAbc9DecGraph( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    char * pFileName = NULL;
    int c, fFile = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFile ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc > globalUtilOptind + 1 )
    {
        return 0;
    }
    if ( !fFile && argc == globalUtilOptind + 1 ) 
    {
        return 0;
    }
    if ( !fFile && pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( fFile && argc == globalUtilOptind + 1 )
    {
        FILE * pFile = fopen( argv[globalUtilOptind], "rb" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9BCore(): Cannot open file \"%s\" for reading the simulation information.\n", argv[globalUtilOptind] );
            return 0;
        }
        fclose( pFile );
        pFileName = argv[globalUtilOptind];
    }
    if ( pFileName ) {
        pTemp = Gia_ManDecGraphFromFile( pFileName );
    } else {
        pTemp = Gia_ManDecGraph( pAbc->pGia );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dg [-vhf] <file>\n" );
    Abc_Print( -2, "\t           convert AIG into decision graph structure\n" );
    Abc_Print( -2, "\t-f       : read from file (in IWLS format) [default = %s]\n" , fFile ? "yes" : "no");
    Abc_Print( -2, "\t-h       : prints the command usage\n\n");
    Abc_Print( -2, "\t           This command was contributed by Jiun-Hao Chen from National Taiwan University.\n" );
    Abc_Print( -2, "\t           For more info, please refer to the paper: Jiun-Hao Chen and Jie-Hong R. Jiang,\n");
    Abc_Print( -2, "\t           \"Circuit learning for multi-output Boolean functions\", Proc. IWLS 2025.\n");
    Abc_Print( -2, "\t           https://people.eecs.berkeley.edu/~alanmi/publications/other/iwls25_dg.pdf\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9QVar( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_QbfQuantifyAll( Gia_Man_t * p, int nPars, int fAndAll, int fOrAll );
    Gia_Man_t * pTemp;
    int c, nPars   = -1;
    int fQuantU    =  0;
    int fQuantE    =  0;
    int fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Puevh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPars < 0 )
                goto usage;
            break;
        case 'u':
            fQuantU ^= 1;
            break;
        case 'e':
            fQuantE ^= 1;
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
        Abc_Print( -1, "There is no current GIA.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Works only for combinational networks.\n" );
        return 1;
    }
    if ( !(nPars > 0 && nPars < Gia_ManPiNum(pAbc->pGia)) )
    {
        Abc_Print( -1, "The number of parameter variables is invalid (should be > 0 and < PI num).\n" );
        return 1;
    }
    pTemp = Gia_QbfQuantifyAll( pAbc->pGia, nPars, fQuantU, fQuantE );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &qvar [-P num] [-uevh]\n" );
    Abc_Print( -2, "\t         derives cofactors w.r.t. the last NumPi-<num> variables\n" );
    Abc_Print( -2, "\t-P num : number of parameters p (should be the first PIs) [default = %d]\n", nPars );
    Abc_Print( -2, "\t-u     : toggle ANDing cofactors (universal quantification) [default = %s]\n", fQuantU? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle ORing cofactors (existential quantification) [default = %s]\n", fQuantE? "yes": "no" );
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
int Abc_CommandAbc9SatFx( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Bmc_FxCompute( Gia_Man_t * p );
    extern int Bmc_FxComputeOne( Gia_Man_t * p, int nIterMax, int nDiv2Add );
    int nIterMax =  5;
    int nDiv2Add = 10;
    int c, fDec  =  1;
    int fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IDdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIterMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDiv2Add = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDiv2Add < 0 )
                goto usage;
            break;
        case 'd':
            fDec ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9SatFx(): There is no AIG.\n" );
        return 0;
    }
    if ( fDec )
        Bmc_FxComputeOne( pAbc->pGia, nIterMax, nDiv2Add );
    else
        Bmc_FxCompute( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &satfx [-ID num] [-dvh]\n" );
    Abc_Print( -2, "\t         performs SAT based shared logic extraction\n" );
    Abc_Print( -2, "\t-I num : the number of iterations of divisor extraction [default = %d]\n", nIterMax );
    Abc_Print( -2, "\t-D num : the number of divisors to extract in each iteration [default = %d]\n", nDiv2Add );
    Abc_Print( -2, "\t-d     : toggles decomposing the first output [default = %s]\n", fDec? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SatClp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Str_t * Bmc_CollapseOne( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fReverse, int fVerbose );
    int nCubeLim = 1000;
    int nBTLimit = 1000000;
    int fCanon   = 0;
    int fVerbose = 0;
    int c;

    Vec_Str_t * vSop;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CLcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubeLim < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
                goto usage;
            break;
        case 'c':
            fCanon ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9SatClp(): There is no AIG.\n" );
        return 0;
    }
    vSop = Bmc_CollapseOne( pAbc->pGia, nCubeLim, nBTLimit, fCanon, 0, fVerbose );
    printf( "%s\n", Vec_StrArray(vSop) );
    Vec_StrFree( vSop );
    return 0;

usage:
    Abc_Print( -2, "usage: &satclp [-CL num] [-cvh]\n" );
    Abc_Print( -2, "\t         performs SAT based collapsing\n" );
    Abc_Print( -2, "\t-C num : the limit on the SOP size of one output [default = %d]\n", nCubeLim );
    Abc_Print( -2, "\t-L num : the limit on the number of conflicts in one SAT call [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-c     : toggles using canonical ISOP computation [default = %s]\n", fCanon? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Esop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Eso_ManCompute( Gia_Man_t * pGia, int fVerbose, Vec_Wec_t ** pvRes );
    Gia_Man_t * pTemp;
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
        Abc_Print( -1, "Abc_CommandAbc9Esop(): There is no AIG.\n" );
        return 0;
    }
    pTemp = Eso_ManCompute( pAbc->pGia, fVerbose, NULL );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &esop [-vh]\n" );
    Abc_Print( -2, "\t         derives Exclusive Sum of Products from AIG\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Exorcism( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_ExorcismMain( Vec_Wec_t * vEsop, int nIns, int nOuts, char * pFileNameOut, int Quality, int Verbosity, int nCubesMax, int fUseQCost );
    extern Vec_Wec_t * Abc_ExorcismNtk2Esop( Abc_Ntk_t * pNtk );

    extern Gia_Man_t * Eso_ManCompute( Gia_Man_t * pGia, int fVerbose, Vec_Wec_t ** pvRes );
    Vec_Wec_t * vEsop = NULL;
    Abc_Ntk_t * pNtk = NULL;
    char * pFileNameIn = NULL;
    char * pFileNameOut = NULL;
    int c, Quality = 2, Verbosity = 0, nCubesMax = 20000, fUseQCost = 0, fVerbose = 0;
    int nInputs = -1, nOutputs = -1;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "QVCqvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            Quality = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Quality < 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            Verbosity = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Verbosity < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubesMax < 0 )
                goto usage;
            break;
        case 'q':
            fUseQCost ^= 1;
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

    if ( argc == globalUtilOptind + 2 )
    {
        pFileNameIn = argv[globalUtilOptind];
        pFileNameOut = argv[globalUtilOptind + 1];
    }
    else if ( argc == globalUtilOptind + 1 )
    {
        pFileNameOut = argv[globalUtilOptind];
    }
    else
    {
        Abc_Print( -1, "Abc_CommandAbc9Exorcism(): Argument error.\n" );
        goto usage;
    }

    if ( pAbc->pGia == NULL && pFileNameIn == NULL )
    {
      Abc_Print( -1, "Abc_CommandAbc9Exorcism(): There is neither an AIG nor an ESOP-PLA file.\n" );
      return 0;
    }

    if ( pFileNameIn )
    {
        // Skip preprocessing and check the result.
        pNtk = Io_ReadPla( pFileNameIn, 0, 0, 0, 1, 1 );
        if ( pNtk == NULL )
        {
            printf( "Reading PLA file has failed.\n" );
            return 1;
        }
        nInputs = Abc_NtkCiNum( pNtk );
        nOutputs = Abc_NtkCoNum( pNtk );
        vEsop = Abc_ExorcismNtk2Esop( pNtk );
        if ( vEsop == NULL )
        {
            printf( "Converting PLA to ESOP failed.\n" );
            return 1;
        }
    }
    else if ( pAbc->pGia )
    {
        // generate starting cover
        nInputs = Gia_ManCiNum( pAbc->pGia );
        nOutputs = Gia_ManCoNum( pAbc->pGia );
        Eso_ManCompute( pAbc->pGia, fVerbose, &vEsop );
    }

    if ( vEsop )
    {
        // run minimization
        Abc_ExorcismMain( vEsop, nInputs, nOutputs, pFileNameOut, Quality, Verbosity, nCubesMax, fUseQCost );
        Vec_WecFree( vEsop );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &exorcism [-Q N] [-V N] [-C N] -q [file_in] <file_out>\n" );
    Abc_Print( -2, "                     performs heuristic exclusive sum-of-project minimization\n" );
    Abc_Print( -2, "        -Q N       : minimization quality [default = %d]\n", Quality);
    Abc_Print( -2, "                     increasing this number improves quality and adds to runtime\n");
    Abc_Print( -2, "        -V N       : verbosity level [default = %d]\n", Verbosity);
    Abc_Print( -2, "                     0 = no output; 1 = outline; 2 = verbose\n");
    Abc_Print( -2, "        -C N       : maximum number of cubes in startign cover [default = %d]\n", nCubesMax );
    Abc_Print( -2, "        -q         : toggle using quantum cost [default = %s]\n", fUseQCost? "yes": "no" );
    Abc_Print( -2, "        [file_in]  : optional input file in ESOP-PLA format (otherwise current AIG is used)\n");
    Abc_Print( -2, "        <file_out> : output file in ESOP-PLA format\n");
    Abc_Print( -2, "\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Odc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupOdc( Gia_Man_t * p, int iObj, int fVerbose );
    Gia_Man_t * pTemp;
    int c, iNode = -1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iNode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iNode < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Odc(): There is no AIG.\n" );
        return 0;
    }
    if ( !Gia_ObjIsAnd( Gia_ManObj(pAbc->pGia, iNode) ) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Odc(): Object with ID %d is not an internal node.\n", iNode );
        return 0;
    }
    pTemp = Gia_ManDupOdc( pAbc->pGia, iNode, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &odc [-N num] [-vh]\n" );
    Abc_Print( -2, "\t          generates the complement of the ODC for the node\n" );
    Abc_Print( -2, "\t-N num  : the node ID [default = undefined]\n" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %d]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9FunAbs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupEncode( Gia_Man_t * p, Vec_Int_t * vVarNums, int fVerbose );
    extern Vec_Int_t * Gia_ManCofClassPattern( Gia_Man_t * p, Vec_Int_t * vVarNums, int fVerbose );
    extern void        Gia_ManCofClassRand( Gia_Man_t * p, int nVars, int nRands );
    extern void        Gia_ManCofClassEnum( Gia_Man_t * p, int nVars );
    Gia_Man_t * pNew = NULL;
    Vec_Int_t * vVars = NULL;
    int c, nVars = 6, nRands = 0, fEnum = 0, fPrint = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KRepvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRands < 0 )
                goto usage;
            break;
        case 'e':
            fEnum ^= 1;
            break;
        case 'p':
            fPrint ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9FunAbs(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) != 1 || Gia_ManRegNum(pAbc->pGia) != 0 ) {
        Abc_Print( -1, "Abc_CommandAbc9FunAbs(): Works only for comb AIGs with one output.\n" );
        return 0;
    }
    if ( nVars >= Gia_ManPiNum(pAbc->pGia) ) {
        Abc_Print( -1, "Abc_CommandAbc9FunAbs(): The number of variables (%d) should be less the PI count (%d).\n", nVars, Gia_ManPiNum(pAbc->pGia) );
        return 0;        
    }
    if ( nRands ) {
        Gia_ManCofClassRand( pAbc->pGia, nVars, nRands );
        return 0;
    }
    if ( fEnum ) {
        Gia_ManCofClassEnum( pAbc->pGia, nVars );
        return 0;
    }
    if ( argc == globalUtilOptind ) {
        vVars = Vec_IntStartNatural( nVars );
        printf( "Abstracting the first %d variables of the AIG.\n", nVars );
    }
    else {
        vVars = Vec_IntAlloc( argc );
        for ( c = globalUtilOptind; c < argc; c++ )
            Vec_IntPush( vVars, atoi(argv[c]) );
        printf( "Abstracting variables: " );
        Vec_IntPrint( vVars );
    }
    if ( fPrint ) {
        Vec_Int_t * vTemp = Gia_ManCofClassPattern( pAbc->pGia, vVars, 1 );
        Vec_IntFree( vTemp );
    } 
    else {
        pNew = Gia_ManDupEncode( pAbc->pGia, vVars, fVerbose );
        Abc_FrameUpdateGia( pAbc, pNew );
    }    
    Vec_IntFree( vVars );
    return 0;

usage:
    Abc_Print( -2, "usage: &funabs [-KR num] [-epvh] <node1> <node2> ... <nodeN>\n" );
    Abc_Print( -2, "\t          generates an abstraction of the function\n" );
    Abc_Print( -2, "\t-K num  : the number of primary inputs [default = %d]\n", nVars );
    Abc_Print( -2, "\t-R num  : the number of random K-set to try [default = %d]\n", nRands );
    Abc_Print( -2, "\t-e      : toggles enumerating bound sets of the given size [default = %s]\n", fEnum ? "yes": "no" );
    Abc_Print( -2, "\t-p      : toggles printing statistics only [default = %s]\n", fPrint ? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<nodes> : the index list of primary inputs to be abstrated\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9DsdInfo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPrintDsdMatrix( Gia_Man_t * p, int iIn );
    extern void Gia_ManCheckDsd( Gia_Man_t * p, int OffSet, int fVerbose );
    extern void Gia_ManRecurDsd( Gia_Man_t * p, int fVerbose );
    int c, iIn = -1, fDsd = 0, fAll = 0, fRecur = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Vdarvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            iIn = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iIn < 0 )
                goto usage;
            break;
        case 'd':
            fDsd ^= 1;
            break;            
        case 'a':
            fAll ^= 1;
            break;
        case 'r':
            fRecur ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9DsdInfo(): There is no AIG.\n" );
        return 0;
    }
    if ( fRecur )
    {
        Gia_ManRecurDsd( pAbc->pGia, fVerbose );
        return 0;
    }
    if ( fDsd ) 
    {
        if ( iIn == -1 ) {
            printf( "Function = " );
            Gia_ManCheckDsd( pAbc->pGia, 0, fVerbose );
            if ( fAll ) {
                for ( iIn = 0; iIn < Gia_ManPiNum(pAbc->pGia); iIn++ )
                    for ( c = 0; c < 2; c++ ) {
                        Gia_Man_t * pTemp = Gia_ManDupCofactorVar( pAbc->pGia, iIn, c );
                        printf( "Cof(%c=%d) = ", 'a' + iIn, c );
                        Gia_ManCheckDsd( pTemp, 12, fVerbose );
                        Gia_ManStop( pTemp );
                    }                
            }
            return 0;
        }
        for ( c = 0; c < 2; c++ ) {
            Gia_Man_t * pTemp = Gia_ManDupCofactorVar( pAbc->pGia, iIn, c );
            printf( "    Cof(%c=%d) = ", 'a' + iIn, c );
            Gia_ManCheckDsd( pTemp, 0, fVerbose );
            if ( fAll ) {
                for ( int iIn2 = 0; iIn2 < Gia_ManPiNum(pAbc->pGia); iIn2++ ) if ( iIn2 != iIn )
                    for ( int c2 = 0; c2 < 2; c2++ ) {
                        Gia_Man_t * pTemp2 = Gia_ManDupCofactorVar( pTemp, iIn2, c2 );
                        printf( "Cof(%c=%d,%c=%d) = ", 'a' + iIn, c, 'a' + iIn2, c2 );
                        Gia_ManCheckDsd( pTemp2, 12, fVerbose );
                        Gia_ManStop( pTemp2 );
                    }
            }
            Gia_ManStop( pTemp );
        }
        return 0;
    }
    if ( iIn < 0 || iIn >= Gia_ManPiNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9DsdInfo(): The input variable is not specified.\n" );
        return 0;
    }
    Gia_ManPrintDsdMatrix( pAbc->pGia, iIn );
    return 0;

usage:
    Abc_Print( -2, "usage: &dsdinfo [-V num] [-drvh]\n" );
    Abc_Print( -2, "\t          computes and displays information related to DSD\n" );
    Abc_Print( -2, "\t-V num  : the zero-based index of the input variable [default = %d]\n", iIn );
    Abc_Print( -2, "\t-d      : toggles showing DSD structure [default = %s]\n", fDsd ? "yes": "no" );
    Abc_Print( -2, "\t-r      : toggles recursive cofactoring to get a full DSD [default = %s]\n", fRecur ? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9FunTrace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Mem_t * Dau_CollectNpnFunctions( word * p, int nVars, int fVerbose );
    extern void Gia_ManMatchCuts( Vec_Mem_t * vTtMem, Gia_Man_t * pGia, int nCutSize, int nCutNum, int fVerbose );
    extern Vec_Mem_t * Abc_TruthDecRead( char * pFileName, int nVarNum );
    extern void Abc_TtStoreDump( char * pFileName, Vec_Mem_t * vTtMem, int nBytes );
    extern Vec_Mem_t * Dau_CollectBoothFunctions( int nLog2Radix );
    int c, nVars, nVars2, nCutNum = 32, nCutSize = 0, nBooth = 0, nNumFuncs = 5, nNumCones = 3, fOutputs = 0, fVerbose = 0; word * pTruth = NULL;
    char * pStr = NULL, * pFuncFileName = "_npn_member_funcs_.data"; Vec_Mem_t * vTtMem = NULL; Gia_Man_t * pTemp;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CKBNMFovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
                goto usage;
            break;            
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutSize < 0 )
                goto usage;
            break;            
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBooth = atoi(argv[globalUtilOptind]);
            if ( nBooth < 4 || nBooth > 1024 ) {
                Abc_Print( -1, "Currently support radix value from 4 to 1024.\n" );
                goto usage;                  
            }
            nBooth = Abc_Base2Log(nBooth);
            if ( (1 << nBooth) != atoi(argv[globalUtilOptind]) ) {
                Abc_Print( -1, "The Booth radix value %s is not a degree of 2.\n", argv[globalUtilOptind] );
                goto usage;                
            }
            globalUtilOptind++;
            break;            
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNumFuncs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNumFuncs < 0 )
                goto usage;
            break;            
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nNumCones = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNumCones < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFuncFileName = argv[globalUtilOptind];
            globalUtilOptind++;
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
        Abc_Print( -1, "Abc_CommandAbc9FunTrace(): There is no AIG.\n" );
        return 0;
    }
    if ( argc == globalUtilOptind )
    {
        if ( nBooth ) {
            vTtMem = Dau_CollectBoothFunctions( nBooth );
            printf( "Generated %d %d-input booth radix-%d encoder functions.\n", 1<<(nBooth-1), nBooth+1, 1<<nBooth );
            nCutSize = nBooth+1;
        }
        else {
            abctime clkStart = Abc_Clock();
            int nFileSize = Gia_FileSize( pFuncFileName );
            if ( nFileSize == 0 )
            {
                Abc_Print( -1, "Abc_CommandAbc9FunTrace(): Truth table in hex notation (or file name with the functions) should be given on the command line.\n" );
                return 0;
            }
            if ( nCutSize == 0 )
            {
                Abc_Print( -1, "Abc_CommandAbc9FunTrace(): The cut size needs to be specified on the command line (-K <num>) when precomputed functions are used.\n" );
                return 0;            
            }
            vTtMem = Abc_TruthDecRead( pFuncFileName, nCutSize );
            printf( "Finished reading %d %d-input function from file \"%s\".  ", nFileSize / 8 / Abc_Truth6WordNum(nCutSize), nCutSize, pFuncFileName );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
        }
        Gia_ManMatchCuts( vTtMem, pAbc->pGia, nCutSize, nCutNum, fVerbose );
        Vec_MemHashFree( vTtMem );
        Vec_MemFree( vTtMem );
        return 0;        
    }
    if ( strstr(argv[globalUtilOptind], ".aig") ) 
    { // the entry on the command line is an AIGER file
        extern void Gia_ManMatchCones( Gia_Man_t * pBig, Gia_Man_t * pSmall, int nCutSize, int nCutNum, int nNumFuncs, int nNumCones, int fVerbose );
        extern void Gia_ManMatchConesOutput( Gia_Man_t * pBig, Gia_Man_t * pSmall, int nCutNum, int fVerbose );
        pTemp = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
        if ( pTemp == NULL ) {
            Abc_Print( -1, "Abc_CommandAbc9FunTrace(): Cannot read input AIG \"%s\".\n", argv[globalUtilOptind] );
            return 0;                
        }
        if ( fOutputs ) {
            if ( Gia_ManCiNum(pTemp) > 16 ) {
                Abc_Print( -1, "Abc_CommandAbc9FunTrace(): The AIG \"%s\" has more than 16 primary inputs.\n", argv[globalUtilOptind] );
                Gia_ManStop( pTemp );
                return 0;                   
            }
            Gia_ManMatchConesOutput( pAbc->pGia, pTemp, nCutNum, fVerbose );
        }
        else  {
            if ( nCutSize == 0 ) {
                Abc_Print( -1, "Abc_CommandAbc9FunTrace(): The LUT size for profiling should be given on the command line.\n" );
                return 0;            
            }
            Gia_ManMatchCones( pAbc->pGia, pTemp, nCutSize, nCutNum, nNumFuncs, nNumCones, fVerbose );
        }
        Gia_ManStop( pTemp );
        return 0;
    }
    pStr = argv[globalUtilOptind];
    if ( pStr[0] == '0' && pStr[1] == 'x' )
        pStr += 2;
    nVars = Abc_Base2Log(strlen(pStr)*4);
    if ( (1 << nVars) != strlen(pStr)*4 )
    {
        Abc_Print( -1, "Abc_CommandAbc9FunTrace(): String \"%s\" does not look like a truth table of a %d-var function.\n", pStr, nVars );
        return 0;
    }
    pTruth = ABC_CALLOC( word, Abc_Truth6WordNum(nVars+1) );
    nVars2 = Abc_TtReadHex( pTruth, pStr );
    if ( nVars != nVars2 )
    {
        ABC_FREE( pTruth );
        Abc_Print( -1, "Abc_CommandAbc9FunTrace(): String \"%s\" does not look like a truth table of a %d-var function.\n", pStr, nVars );
        return 0;
    }
    //Abc_TtPrintHexRev( stdout, pTruth, nVars ); printf( "\n" );
    vTtMem = Dau_CollectNpnFunctions( pTruth, nVars, fVerbose );
    Gia_ManMatchCuts( vTtMem, pAbc->pGia, nVars, nCutNum, fVerbose );
    if ( pFuncFileName ) {
        Abc_TtStoreDump( pFuncFileName, vTtMem, 8 * Vec_MemEntrySize(vTtMem) );
        printf( "Dumped %d NPN class member functions into file \"%s\".\n", Vec_MemEntryNum(vTtMem), pFuncFileName );
    }
    Vec_MemHashFree( vTtMem );
    Vec_MemFree( vTtMem );
    return 0;

usage:
    Abc_Print( -2, "usage: &funtrace [-CKBNM num] [-F file] [-ovh] {<truth> or <file.aig>}\n" );
    Abc_Print( -2, "\t          traces the presence of the function in the current AIG\n" );
    Abc_Print( -2, "\t-C num  : the number of cuts to compute at each node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-K num  : the LUT size to use when <file.aig> is given [default = %d]\n", nCutSize );
    Abc_Print( -2, "\t-B num  : the radix of booth partial products to detect [default = %d]\n", nBooth );
    Abc_Print( -2, "\t-N num  : the number of functions to use when <file.aig> or -F <file> are used [default = %d]\n", nNumFuncs );
    Abc_Print( -2, "\t-M num  : the number of logic cones to use when <file.aig> is given [default = %d]\n", nNumCones );
    Abc_Print( -2, "\t-F file : the file name to store the NPN member functions [default = %s]\n", pFuncFileName );
    Abc_Print( -2, "\t-o      : toggles using AIG output functions instead of frequent cut functions [default = %s]\n", fOutputs ? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<truth> : truth table in the hexadecimal notation used for tracing\n");
    Abc_Print( -2, "\t<file>  : AIG whose K-input functions will be used for tracing\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Cuts( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManComputeCutsCore( Gia_Man_t * pGia, int nCutSize0, int nCutNum0, int fTruth0, int fVerbose0, int fDumpText, int fDumpBin, char * pFileName );
    int nCutSize =  6;
    int nCutNum  = 16;
    int fTruth   =  1;
    int fVerbose =  1;
    int fDumpText = 0;
    int fDumpBin  = 0;
    int c;
    char * pFileName = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCtdbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutSize < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
                goto usage;
            break;
        case 't':
            fTruth ^= 1;
            break;
        case 'd':
            fDumpText ^= 1;
            break;
        case 'b':
            fDumpBin ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Cuts(): There is no AIG.\n" );
        return 0;
    }
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else if ( argc != globalUtilOptind )
    {
        Abc_Print( 1,"Abc_CommandAbc9Cuts(): Trailing arguments on the command line.\n" );
        return 0;
    }
    if ( nCutSize < 2 || nCutSize > 14 )
    {
        Abc_Print( -1, "The number of cut leaves should belong to the range: %d <= K <= %d.\n", 2, 14 );
        return 1;
    }
    if ( nCutNum < 2 || nCutNum > 256 )
    {
        Abc_Print( -1, "The number of cuts per node should belong to the range: %d <= C <= %d.\n", 2, 256 );
        return 1;
    }
    if ( fDumpBin && !pFileName )
    {
        Abc_Print( -1, "Output binary file name should be provided on the command line.\n" );
        return 1;
    }
    Gia_ManComputeCutsCore( pAbc->pGia, nCutSize, nCutNum, fTruth, fVerbose, fDumpText, fDumpBin, pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: &cuts [-KC num] [-tdbvh]\n" );
    Abc_Print( -2, "\t         computes K-input cuts for the nodes in the current AIG\n" );
    Abc_Print( -2, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n", 2, 14, nCutSize );
    Abc_Print( -2, "\t-C num : max number of cuts at a node (%d <= num <= %d) [default = %d]\n", 2, 256, nCutNum );
    Abc_Print( -2, "\t-t     : toggle truth table computation and cut minimization [default = %s]\n", fTruth? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dumping cuts into a text file [default = %s]\n", fDumpText? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fDumpBin? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
