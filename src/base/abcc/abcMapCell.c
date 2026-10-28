/**CFile****************************************************************

  FileName    [abcMapCell.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Cell mapping and physical optimization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "map/amap/amap.h"
#include "map/mio/mio.h"
#include "map/scl/sclCon.h"
#include "opt/mfs/mfs.h"
#include "opt/sfm/sfm.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandMfs3                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGlitch                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPowerdown              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAddBuffs               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMap                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAmap                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPhaseMap               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandStochMap               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnmap                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAttach                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoice            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTimeScale              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqMap                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Force              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Embed              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Nf2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Nf3                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Nf                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Simap              ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers cell mapping and physical optimization commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitMapCell( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "mfsmap",        Abc_CommandMfs3,             1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "glitch",        Abc_CommandGlitch,           0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "powerdown",     Abc_CommandPowerdown,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "addbuffs",      Abc_CommandAddBuffs,         1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "map",           Abc_CommandMap,              1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "amap",          Abc_CommandAmap,             1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "phase_map",     Abc_CommandPhaseMap,         1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "stochmap",      Abc_CommandStochMap,         1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "unmap",         Abc_CommandUnmap,            1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "attach",        Abc_CommandAttach,           1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "superc",        Abc_CommandSuperChoice,      1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "timescale",     Abc_CommandTimeScale,        0 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "smap",          Abc_CommandSeqMap,           1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&force",        Abc_CommandAbc9Force,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&embed",        Abc_CommandAbc9Embed,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&nf2",          Abc_CommandAbc9Nf2,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&nf3",          Abc_CommandAbc9Nf3,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&nf",           Abc_CommandAbc9Nf,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&simap",        Abc_CommandAbc9Simap,        0 );
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
int Abc_CommandMfs3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkPerformMfs3Rounds( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars, int nIters );
    extern void Sfm_ParSetDefault3( Sfm_Par_t * pPars );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    Sfm_Par_t Pars, * pPars = &Pars; int c;
    int fAreaOnly = 0, fDelayOnly = 0, fKeepTiming = 0, nIters = 1;
    // set defaults
    Sfm_ParSetDefault3( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "RIOVFKLHSMCNPWDETarmzespdtlvwh" ) ) != EOF )
    {
        if ( (c == 'R' || c == 'I' || c == 'S' || c == 'N' || c == 'P') && globalUtilOptind < argc )
        {
            char * pEnd;
            long Value;
            int fPositive = c == 'R' || c == 'I' || c == 'S';
            errno = 0;
            Value = strtol( argv[globalUtilOptind], &pEnd, 10 );
            if ( errno == ERANGE || pEnd == argv[globalUtilOptind] || *pEnd || Value < fPositive || Value > INT_MAX )
            {
                Abc_Print( -1, "Command line switch \"-%c\" requires a %s integer.\n", c, fPositive ? "positive" : "nonnegative" );
                goto usage;
            }
        }
        switch ( c )
        {
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfiLevMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfoLevMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfoLevMax < 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfiLevMax = pPars->nTfoLevMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfiLevMax < 1 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFanoutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFanoutMax < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVarMax < 2 || pPars->nVarMax > 8 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMffcMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMffcMin < 0 )
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMffcMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMffcMax < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDecMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDecMax < 1 || pPars->nDecMax > 4 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinSizeMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodesMax < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->iNodeOne = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->iNodeOne < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeWin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeWin < 0 || pPars->nTimeWin > 100 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->DeltaCrit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DeltaCrit < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->DelAreaRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelAreaRatio < 0 )
                goto usage;
            break;
        case 'a':
            fAreaOnly = 1;
            break;
        case 'r':
            pPars->fAreaRev ^= 1;
            break;
        case 't':
            fKeepTiming = 1;
            break;
        case 'm':
            pPars->fUseAndOr ^= 1;
            break;
        case 'z':
            pPars->fZeroCost ^= 1;
            break;
        case 'e':
            pPars->fMoreEffort ^= 1;
            break;
        case 's':
            pPars->fUseSim ^= 1;
            break;
        case 'p':
            pPars->fPrintDecs ^= 1;
            break;
        case 'd':
            fDelayOnly = 1;
            break;
        case 'T':
            pPars->fDelayVerbose ^= 1;
            break;
        case 'l':
            pPars->fLibVerbose ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fDelayOnly && (fAreaOnly || fKeepTiming) )
    {
        Abc_Print( -1, "Delay optimization (-d) cannot be combined with area-mode switches (-a or -t).\n" );
        goto usage;
    }
    // Resolve mode selectors independently of their order. Keep -at as an
    // explicit spelling of the default for compatibility with earlier scripts.
    pPars->fArea = !fDelayOnly;
    pPars->fAreaTiming = !fDelayOnly && (!fAreaOnly || fKeepTiming);
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsMappedLogic(pNtk) )
    {
        char Command[5], * pArgv[2] = { Command, NULL };
        int fUseAmap = pPars->fArea && !pPars->fAreaTiming, fMapFailed;
        strcpy( Command, fUseAmap ? "amap" : "map" );
        if ( pPars->fVerbose )
            Abc_Print( 1, "Mapping the input using %s.\n", Command );
        // Reuse mapper defaults, input conversion, and failure handling.
        fMapFailed = fUseAmap ? Abc_CommandAmap(pAbc, 1, pArgv) : Abc_CommandMap(pAbc, 1, pArgv);
        if ( fMapFailed && !fUseAmap )
            return 1;
        pNtk = Abc_FrameReadNtk(pAbc);
        if ( fUseAmap && (fMapFailed || Abc_NtkGetFaninMax(pNtk) > 6) )
        {
            if ( fMapFailed )
                Abc_Print( 1, "Automatic amap mapping failed; retrying with map.\n" );
            else if ( pPars->fVerbose )
                Abc_Print( 1, "The amap result uses gates with more than 6 inputs; retrying with map.\n" );
            strcpy( Command, "map" );
            if ( Abc_CommandMap(pAbc, 1, pArgv) )
                return 1;
            pNtk = Abc_FrameReadNtk(pAbc);
        }
    }
    if ( Abc_NtkGetFaninMax(pNtk) > 6 )
    {
        Abc_Print( -1, "mfsmap requires mapped gates with at most 6 inputs.\n" );
        return 1;
    }
    // modify the current network
    pNtkRes = Abc_NtkPerformMfs3Rounds( pNtk, pPars, nIters );
    if ( pNtkRes == NULL )
        return 1;
    if ( pNtkRes != pNtk )
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: mfsmap [-a|-d] [-RIOVFKLHSMCNPWDE <num>] [-trmzespTlvwh]\n" );
    Abc_Print( -2, "\t           performs don't-care-based optimization of mapped networks\n" );
    Abc_Print( -2, "\t           minimizes area while preserving initial GENLIB block delay by default\n" );
    Abc_Print( -2, "\t-R <num> : max complete optimization iterations (1 <= num) [default = %d]\n",            nIters );
    Abc_Print( -2, "\t           stop at the first iteration without improvement of the selected objective\n" );
    Abc_Print( -2, "\t-I <num> : TFI cone levels (1 <= num) [default = %d]\n",                                pPars->nTfiLevMax );
    Abc_Print( -2, "\t-O <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             pPars->nTfoLevMax );
    Abc_Print( -2, "\t-V <num> : the number of levels in the TFI/TFO cone (1 <= num) [default = %d]\n",         pPars->nTfiLevMax );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                pPars->nFanoutMax );
    Abc_Print( -2, "\t-K <num> : the max number of variables (2 <= num <= 8 ) [default = %d]\n",                pPars->nVarMax );
    Abc_Print( -2, "\t-L <num> : the min size of max fanout-free cone (MFFC) (area-only) [default = %d]\n",     pPars->nMffcMin );
    Abc_Print( -2, "\t-H <num> : the max size of max fanout-free cone (MFFC) (area-only) [default = %d]\n",     pPars->nMffcMax );
    Abc_Print( -2, "\t-S <num> : max decomposition attempts per node (1 <= num <= 4) [default = %d]\n",         pPars->nDecMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    pPars->nWinSizeMax );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   pPars->nBTLimit );
    Abc_Print( -2, "\t-N <num> : max nodes to try per iteration (0 = all) [default = %d]\n",                    pPars->nNodesMax );
    Abc_Print( -2, "\t-P <num> : one particular node to try (0 = none) [default = %d]\n",                       pPars->iNodeOne );
    Abc_Print( -2, "\t-W <num> : size of timing window in percents (0 <= num <= 100) [default = %d]\n",         pPars->nTimeWin );
    Abc_Print( -2, "\t-D <num> : size of critical-timing delay-delta (in picoseconds) [default = %d]\n",        pPars->DeltaCrit );
    Abc_Print( -2, "\t-E <num> : delay-area tradeoff (in picoseconds per area-unit) [default = %d]\n",          pPars->DelAreaRatio );
    Abc_Print( -2, "\t-a       : minimize area without a delay constraint\n" );
    Abc_Print( -2, "\t-d       : minimize delay; allow area growth only if delay decreases (except with -P)\n" );
    Abc_Print( -2, "\t-t       : preserve initial GENLIB delay in area mode (default; overrides -a)\n" );
    Abc_Print( -2, "\t-r       : toggle using reverse topo order for area minimization [default = %s]\n",       pPars->fAreaRev? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggle detecting multi-input AND/OR gates [default = %s]\n",                   pPars->fUseAndOr? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle zero-cost replacements [default = %s]\n",                               pPars->fZeroCost? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggle using more effort [default = %s]\n",                                    pPars->fMoreEffort? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle using simulation [default = %s]\n",                                     pPars->fUseSim? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggle printing decompositions [default = %s]\n",                              pPars->fPrintDecs? "yes": "no" );
    Abc_Print( -2, "\t-T       : toggle printing delay profile statistics [default = %s]\n",                    pPars->fDelayVerbose? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggle printing library usage statistics [default = %s]\n",                    pPars->fLibVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGlitch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nPats    = 4000;
    int Prob     =    8;
    int fVerbose =    1;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NPvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nPats = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPats < 1 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Prob = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Prob < 1 )
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
        Abc_Print( -1, "This command can only be applied to a mapped logic network.\n" );
        return 1;
    }
    if ( Abc_NtkIsMappedLogic(pNtk) || Abc_NtkGetFaninMax(pNtk) <= 6 )
        Abc_Print( 1, "Glitching adds %7.2f %% of signal transitions, compared to switching.\n", Abc_NtkMfsTotalGlitching(pNtk, nPats, Prob, fVerbose) );
    else
        printf( "Currently computes glitching only for K-LUT networks with K <= 6.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: glitch [-NP <num>] [-vh]\n" );
    Abc_Print( -2, "\t           comparing glitching activity to switching activity\n" );
    Abc_Print( -2, "\t-N <num> : the number of random patterns to use (0 < num < 1000000) [default = %d]\n", nPats );
    Abc_Print( -2, "\t-P <num> : once in how many cycles an input changes its value [default = %d]\n", Prob );
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
int Abc_CommandPowerdown( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int fVeryVerbose;
    extern Abc_Ntk_t * Abc_NtkPowerdown( Abc_Ntk_t * pNtk, int fUseLutLib, int Percentage, int Degree, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUseLutLib = 0;
    Percentage =10;
    Degree     = 2;
    fVerbose   = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PNlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Percentage = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Percentage < 1 || Percentage > 100 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            Degree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Degree < 1 || Degree > 5 )
                goto usage;
            break;
        case 'l':
            fUseLutLib ^= 1;
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
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    pNtkRes = Abc_NtkPowerdown( pNtk, fUseLutLib, Percentage, Degree, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: powerdown [-PN <num>] [-vwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to power down the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : switching propability delta defining power critical edges [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t           (e.g. 5% means hot wires switch with probability: 0.45 <= p <= 0.50 (max)\n" );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
//    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAddBuffs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkAddBuffs( Abc_Ntk_t * pNtk, int fDirect, int fReverse, int nImprove, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int fDirect;
    int fReverse;
    int nImprove;
    int c, fVerbose;

    fDirect  = 0;
    fReverse = 0;
    nImprove = 1000;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Idrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nImprove = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nImprove < 0 )
                goto usage;
            break;
        case 'd':
            fDirect ^= 1;
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

    // modify the current network
    pNtkRes = Abc_NtkAddBuffs( pNtk, fDirect, fReverse, nImprove, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: addbuffs [-I num] [-drvh]\n" );
    Abc_Print( -2, "\t           adds buffers to create balanced CI/CO paths\n" );
    Abc_Print( -2, "\t-I <num> : the number of refinement iterations [default = %d]\n", nImprove );
    Abc_Print( -2, "\t-d       : toggle using only CI-to-CO levelized order [default = %s]\n", fDirect? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggle using only CO-to-C1 levelized order [default = %s]\n", fReverse? "yes": "no" );
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
int Abc_CommandMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    char Buffer[100];
    double DelayTarget;
    double AreaMulti;
    double DelayMulti;
    float LogFan = 0;
    float Slew = 0; // choose based on the library
    float Gain = 250;
    int nGatesMin = 0;
    int fAreaOnly;
    int fRecovery;
    int fSweep;
    int fSwitching;
    int fSkipFanout;
    int fUseProfile;
    int fUseBuffs;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkMap( Abc_Ntk_t * pNtk, Mio_Library_t* userLib, double DelayTarget, double AreaMulti, double DelayMulti, float LogFan, float Slew, float Gain, int nGatesMin, int fRecovery, int fSwitching, int fSkipFanout, int fUseProfile, int fUseBuffs, int fVerbose );
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    DelayTarget =-1;
    AreaMulti   = 0;
    DelayMulti  = 0;
    fAreaOnly   = 0;
    fRecovery   = 1;
    fSweep      = 0;
    fSwitching  = 0;
    fSkipFanout = 0;
    fUseProfile = 0;
    fUseBuffs   = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "DABFSGMarspfuovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayTarget <= 0.0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a floating point number.\n" );
                goto usage;
            }
            AreaMulti = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayMulti = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a floating point number.\n" );
                goto usage;
            }
            LogFan = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LogFan < 0.0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a floating point number.\n" );
                goto usage;
            }
            Slew = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Slew <= 0.0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a floating point number.\n" );
                goto usage;
            }
            Gain = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Gain <= 0.0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nGatesMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nGatesMin < 0 )
                goto usage;
            break;
        case 'a':
            fAreaOnly ^= 1;
            break;
        case 'r':
            fRecovery ^= 1;
            break;
        case 's':
            fSweep ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
            break;
        case 'f':
            fSkipFanout ^= 1;
            break;
        case 'u':
            fUseProfile ^= 1;
            break;
        case 'o':
            fUseBuffs ^= 1;
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

    if ( fAreaOnly )
        DelayTarget = ABC_INFINITY;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 0, "The network was strashed and balanced before mapping.\n" );
        // get the new network
        // Use the default mapping library.
        pNtkRes = Abc_NtkMap( pNtk, NULL, DelayTarget, AreaMulti, DelayMulti, LogFan, Slew, Gain, nGatesMin, fRecovery, fSwitching, fSkipFanout, fUseProfile, fUseBuffs, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        // Use the default mapping library.
        pNtkRes = Abc_NtkMap( pNtk, NULL, DelayTarget, AreaMulti, DelayMulti, LogFan, Slew, Gain, nGatesMin, fRecovery, fSwitching, fSkipFanout, fUseProfile, fUseBuffs, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
    }

    if ( fSweep )
    {
        Abc_NtkFraigSweep( pNtkRes, 0, 0, 0, 0 );
        if ( Abc_NtkHasMapping(pNtkRes) )
        {
            pNtkRes = Abc_NtkDupDfs( pNtk = pNtkRes );
            Abc_NtkDelete( pNtk );
        }
    }

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 )
        sprintf(Buffer, "not used" );
    else
        sprintf(Buffer, "%.3f", DelayTarget );
    Abc_Print( -2, "usage: map [-DABFSG float] [-M num] [-arspfuovh]\n" );
    Abc_Print( -2, "\t           performs standard cell mapping of the current network\n" );
    Abc_Print( -2, "\t-D float : sets the global required times [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-A float : \"area multiplier\" to bias gate selection [default = %.2f]\n", AreaMulti );
    Abc_Print( -2, "\t-B float : \"delay multiplier\" to bias gate selection [default = %.2f]\n", DelayMulti );
    Abc_Print( -2, "\t-F float : the logarithmic fanout delay parameter [default = %.2f]\n", LogFan );
    Abc_Print( -2, "\t-S float : the slew parameter used to generate the library [default = %.2f]\n", Slew );
    Abc_Print( -2, "\t-G float : the gain parameter used to generate the library [default = %.2f]\n", Gain );
    Abc_Print( -2, "\t-M num   : skip gate classes whose size is less than this [default = %d]\n", nGatesMin );
    Abc_Print( -2, "\t-a       : toggles area-only mapping [default = %s]\n", fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    Abc_Print( -2, "\t-p       : optimizes power by minimizing switching [default = %s]\n", fSwitching? "yes": "no" );
    Abc_Print( -2, "\t-f       : do not use large gates to map high-fanout nodes [default = %s]\n", fSkipFanout? "yes": "no" );
    Abc_Print( -2, "\t-u       : use standard-cell profile [default = %s]\n", fUseProfile? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles using buffers to decouple combinational outputs [default = %s]\n", fUseBuffs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Amap_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fSweep;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarAmap( Abc_Ntk_t * pNtk, Amap_Par_t * pPars );
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSweep = 0;
    Amap_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FACEQmxisvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nIterFlow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterFlow < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nIterArea = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterArea < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->fEpsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->fEpsilon < 0.0 || pPars->fEpsilon > 1.0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->fADratio = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->fADratio < 0.0 )
                goto usage;
            break;
        case 'm':
            pPars->fUseMuxes ^= 1;
            break;
        case 'x':
            pPars->fUseXors ^= 1;
            break;
        case 'i':
            pPars->fFreeInvs ^= 1;
            break;
        case 's':
            fSweep ^= 1;
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 0, "The network was strashed and balanced before mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkDarAmap( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkDarAmap( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
    }

    if ( fSweep )
    {
        Abc_NtkFraigSweep( pNtkRes, 0, 0, 0, 0 );
        if ( Abc_NtkHasMapping(pNtkRes) )
        {
            pNtkRes = Abc_NtkDupDfs( pNtk = pNtkRes );
            Abc_NtkDelete( pNtk );
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: amap [-FAC <num>] [-EQ <float>] [-mxisvh]\n" );
    Abc_Print( -2, "\t           performs standard cell mapping of the current network\n" );
    Abc_Print( -2, "\t-F num   : the number of iterations of area flow [default = %d]\n", pPars->nIterFlow );
    Abc_Print( -2, "\t-A num   : the number of iterations of exact area [default = %d]\n", pPars->nIterArea );
    Abc_Print( -2, "\t-C num   : the maximum number of cuts at a node [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->fEpsilon );
    Abc_Print( -2, "\t-Q float : area/delay preference ratio [default = %.2f (area-only)] \n", pPars->fADratio );
    Abc_Print( -2, "\t-m       : toggles using MUX matching [default = %s]\n", pPars->fUseMuxes? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles using XOR matching [default = %s]\n", pPars->fUseXors? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles assuming inverters are free [default = %s]\n", pPars->fFreeInvs? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPhaseMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkChangePerform( Abc_Ntk_t * pNtk, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fVerbose = 0, c;
    // set defaults
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
    if ( !Abc_NtkHasMapping(pNtk) )
    {
        Abc_Print( -1, "Cannot unmap the network that is not mapped.\n" );
        return 1;
    }
    Abc_NtkChangePerform( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: phase_map [-vh]\n" );
    Abc_Print( -2, "\t        tries to replace each gate by its complement (area-only)\n" );
    Abc_Print( -2, "\t-v    : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandStochMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes = NULL, * pNtk = Abc_FrameReadNtk(pAbc);
    extern void Mio_IntallAndLibrary();    
    extern void Abc_NtkStochMap( int nSuppMax, int nIters, int TimeOut, int Seed, int fOverlap, int fVerbose, char * pScript, int nProcs );
    int c, nMaxSize = 14, nIters = 1, TimeOut = 0, Seed = 0, nProcs = 1, fOverlap = 0, fVerbose = 0; char * pScript;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NITSPovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxSize < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 )
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
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProcs < 0 )
                goto usage;
            break;            
        case 'o':
            fOverlap ^= 1;
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
        Abc_Print( -1, "Abc_CommandStochMap(): There is no AIG.\n" );
        return 0;
    }
    if ( Abc_NtkIsStrash(pNtk) ) 
    {
        extern Abc_Ntk_t * Abc_NtkDarAmap( Abc_Ntk_t * pNtk, Amap_Par_t * pPars );
        Amap_Par_t Pars, * pPars = &Pars;
        Amap_ManSetDefaultParams( pPars );
        Mio_IntallAndLibrary();
        pNtkRes = Abc_NtkDarAmap( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        pNtk = Abc_FrameReadNtk(pAbc);
    }
    if ( !Abc_NtkIsMappedLogic(pNtk) )
    {
        Abc_Print( -1, "Abc_CommandStochMap(): Expecting a mapped current newtork as input.\n" );
        return 0;
    }    
    if ( argc != globalUtilOptind + 1 )
    {
        printf( "Expecting a synthesis script in quotes on the command line (for example: \"&st; &dch; &if\").\n" );
        goto usage;
    }
    pScript = Abc_UtilStrsav( argv[globalUtilOptind] );
    Abc_NtkStochMap( nMaxSize, nIters, TimeOut, Seed, fOverlap, fVerbose, pScript, nProcs );
    ABC_FREE( pScript );
    if ( pNtkRes )
    {
        pNtk = Abc_FrameReadNtk(pAbc);
        pNtkRes = Abc_NtkStrash( pNtk, 1, 1, 0 );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Strashing has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: stochmap [-NITSP <num>] [-ovh] <script>\n" );
    Abc_Print( -2, "\t           performs stochastic mapping\n" );
    Abc_Print( -2, "\t-N <num> : the max support size of a partition [default = %d]\n",        nMaxSize );
    Abc_Print( -2, "\t-I <num> : the number of optimization iterations [default = %d]\n",      nIters  );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds (0 = no timeout) [default = %d]\n",    TimeOut );
    Abc_Print( -2, "\t-S <num> : user-specified random seed (0 <= num <= 100) [default = %d]\n", Seed  );
    Abc_Print( -2, "\t-P <num> : the number of concurrent processes (1 <= num <= 100) [default = %d]\n", nProcs );
    Abc_Print( -2, "\t-o       : toggle using overlapping partitions [default = %s]\n",        fOverlap? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",       fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<script> : synthesis script to use for each partition\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(pNtk) )
    {
        Abc_Print( -1, "Cannot unmap the network that is not mapped.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkMapToSop( pNtk ) )
    {
        Abc_Print( -1, "Unmapping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: unmap [-h]\n" );
    Abc_Print( -2, "\t        replaces the library gates by the logic nodes represented using SOPs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAttach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Can only attach gates if the nodes have SOP representations.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkAttach( pNtk ) )
    {
        Abc_Print( -1, "Attaching gates has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: attach [-h]\n" );
    Abc_Print( -2, "\t        replaces the SOP functions by the gates from the library\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSuperChoice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkSuperChoice( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkSuperChoice( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: superc [-h]\n" );
    Abc_Print( -2, "\t      performs superchoicing\n" );
    Abc_Print( -2, "\t      (accumulate: \"r file.blif; rsup; b; sc; f -ac; wb file_sc.blif\")\n" );
    Abc_Print( -2, "\t      (map without supergate library: \"r file_sc.blif; ft; map\")\n" );
    Abc_Print( -2, "\t-h  : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTimeScale( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkTimeScale( Abc_Ntk_t * pNtk, float Scale );
    Abc_Ntk_t * pNtk;
    float nTimeScale;
    int c, fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nTimeScale = (float)0.01;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Th" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeScale = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeScale < 0 )
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
    if ( pNtk->pManTime == NULL )
    {
        Abc_Print( -1, "Timing manager is not defined.\n" );
        return 1;
    }
    Abc_NtkTimeScale( pNtk, nTimeScale );
    return 0;

usage:
    Abc_Print( -2, "usage: timescale [-T float] [-vh]\n" );
    Abc_Print( -2, "\t           scales timing information of the current network\n" );
    Abc_Print( -2, "\t-T float : multiplicative factor [default = %f]\n", nTimeScale );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    int c, nMaxIters;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nMaxIters = 15;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 )
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

    if ( Abc_NtkHasAig(pNtk) )
    {
//        // quit if there are choice nodes
//        if ( Abc_NtkGetChoiceNum(pNtk) )
//        {
//            Abc_Print( -1, "Currently cannot map/retime networks with choice nodes.\n" );
//            return 0;
//        }
//        if ( Abc_NtkIsStrash(pNtk) )
//            pNtkNew = Abc_NtkAigToSeq(pNtk);
//        else
//            pNtkNew = Abc_NtkDup(pNtk);
        pNtkNew = NULL;
    }
    else
    {
        // strash and balance the network
        pNtkNew = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Strashing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Balancing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Converting into a seq AIG before SC mapping/retiming has failed.\n" );
            return 1;
        }

        Abc_Print( -1, "The network was strashed and balanced before SC mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_MapRetime( pNtkNew, nMaxIters, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
//        Abc_Print( -1, "Sequential FPGA mapping has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return 0;
    }
    Abc_NtkDelete( pNtkNew );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: smap [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         performs integrated sequential standard-cell mapping/retiming\n" );
    Abc_Print( -2, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
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
int Abc_CommandAbc9Force( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int nIters     = 20;
    int fClustered =  1;
    int fVerbose   =  1;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Icvh" ) ) != EOF )
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
            if ( nIters < 0 )
                goto usage;
            break;
        case 'c':
            fClustered ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Force(): There is no AIG.\n" );
        return 1;
    }
    For_ManExperiment( pAbc->pGia, nIters, fClustered, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &force [-I <num>] [-cvh]\n" );
    Abc_Print( -2, "\t         one-dimensional placement algorithm FORCE introduced by\n" );
    Abc_Print( -2, "\t         F. A. Aloul, I. L. Markov, and K. A. Sakallah (GLSVLSI�03).\n" );
    Abc_Print( -2, "\t-I num : the number of refinement iterations [default = %d]\n", nIters );
    Abc_Print( -2, "\t-c     : toggle clustered representation [default = %s]\n", fClustered? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Embed( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Emb_Par_t Pars, * pPars = &Pars;
    int c;
    pPars->nDims      = 30;
    pPars->nIters     = 10;
    pPars->nSols      =  2;
    pPars->fRefine    =  0;
    pPars->fCluster   =  0;
    pPars->fDump      =  0;
    pPars->fDumpLarge =  0;
    pPars->fShowImage =  0;
    pPars->fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "DIrcdlsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDims = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDims < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIters < 0 )
                goto usage;
            break;
        case 'r':
            pPars->fRefine ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 'd':
            pPars->fDump ^= 1;
            break;
        case 'l':
            pPars->fDumpLarge ^= 1;
            break;
        case 's':
            pPars->fShowImage ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Embed(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManSolveProblem( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &embed [-DI <num>] [-rdlscvh]\n" );
    Abc_Print( -2, "\t         fast placement based on high-dimensional embedding from\n" );
    Abc_Print( -2, "\t         D. Harel and Y. Koren, \"Graph drawing by high-dimensional\n" );
    Abc_Print( -2, "\t         embedding\", J. Graph Algs & Apps, 2004, Vol 8(2), pp. 195-217\n" );
    Abc_Print( -2, "\t-D num : the number of dimensions for embedding [default = %d]\n", pPars->nDims );
    Abc_Print( -2, "\t-I num : the number of refinement iterations [default = %d]\n", pPars->nIters );
    Abc_Print( -2, "\t-r     : toggle the use of refinement [default = %s]\n", pPars->fRefine? "yes":"no");
    Abc_Print( -2, "\t-c     : toggle clustered representation [default = %s]\n", pPars->fCluster? "yes":"no");
    Abc_Print( -2, "\t-d     : toggle dumping placement into a Gnuplot file [default = %s]\n", pPars->fDump? "yes":"no");
    Abc_Print( -2, "\t-l     : toggle dumping Gnuplot for large placement [default = %s]\n", pPars->fDumpLarge? "yes":"no");
    Abc_Print( -2, "\t-s     : toggle showing image if Gnuplot is installed [default = %s]\n", pPars->fShowImage? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Nf2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew;
    char * pEnd;
    long Value;
    double Delay;
    int c, fTied = 0;
    Nf2_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KCFADapqtvh")) != EOF )
    {
        switch ( c )
        {
        case 'K':
        case 'C':
        case 'F':
        case 'A':
            if ( globalUtilOptind >= argc ) goto usage;
            Value = strtol( argv[globalUtilOptind], &pEnd, 10 );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || Value < 0 || Value > 1000 ) goto usage;
            globalUtilOptind++;
            if ( c == 'K' )
            {
                if ( Value < 2 || Value > 6 ) goto usage;
                pPars->nLutSize = (int)Value;
            }
            else if ( c == 'C' )
            {
                if ( Value < 2 || Value > pPars->nCutNumMax ) goto usage;
                pPars->nCutNum = (int)Value;
            }
            else if ( c == 'F' ) { if ( Value < 1 ) goto usage; pPars->nRounds = (int)Value; }
            else pPars->nRoundsEla = (int)Value;
            break;
        case 'D':
            if ( globalUtilOptind >= argc ) goto usage;
            Delay = strtod( argv[globalUtilOptind], &pEnd );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || !(Delay >= 1.0/SCL_NUM && Delay < (double)SCL_INFINITY/SCL_NUM) ) goto usage;
            globalUtilOptind++;
            pPars->MapDelayTarget = (int)(Delay * SCL_NUM);
            break;
        case 'a': pPars->fAreaOnly ^= 1; break;
        case 'p': pPars->fPinPerm ^= 1; break;
        case 'q': pPars->fPinQuick ^= 1; break;
        case 't': fTied ^= 1; break;
        case 'v': pPars->fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( Abc_FrameReadLibGen() == NULL )
    {
        Abc_Print( -1, "Current library is not available.\n" );
        return 1;
    }
    pNew = fTied ? Nf2_ManPerformMappingTied( pAbc->pGia, pPars ) : Nf2_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Nf2(): standard-cell mapping has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &nf2 [-KCFA num] [-D float] [-apqtvh]\n" );
    Abc_Print( -2, "\t           performs library-guided standard-cell mapping on the GIA\n" );
    Abc_Print( -2, "\t-K num   : the maximum cut size (2 <= num <= 6) [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the maximum retained cuts (2 <= num <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : the number of delay and area flow rounds [default = %d]\n", pPars->nRounds < 0 ? 1 : pPars->nRounds );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations [default = %d]\n", pPars->nRoundsEla < 0 ? 1 : pPars->nRoundsEla );
    Abc_Print( -2, "\t           choice inputs default to 2 exact area recovery iterations\n" );
    Abc_Print( -2, "\t           reference fallback defaults to 4 flow and 2 exact area rounds\n" );
    Abc_Print( -2, "\t-D float : sets the mapping delay constraint [default = best found]\n" );
    Abc_Print( -2, "\t-a       : toggles area-only mapping (ignores delay constraints) [default = %s]\n", pPars->fAreaOnly ? "yes" : "no" );
    Abc_Print( -2, "\t-p       : toggles pin permutations [default = %s]\n", pPars->fPinPerm ? "yes" : "no" );
    Abc_Print( -2, "\t-q       : toggles quick matching [default = %s]\n", pPars->fPinQuick ? "yes" : "no" );
    Abc_Print( -2, "\t-t       : toggles library preprocessing for constant/repeated pins [default = %s]\n", fTied ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs standard-cell mapping with structural area recovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Nf3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew;
    char * pEnd;
    long Value;
    double Delay;
    int c, fSynthesis = 1, nRecover = 1;
    Nf3_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KCFARDasvh")) != EOF )
    {
        switch ( c )
        {
        case 'K':
        case 'C':
        case 'F':
        case 'A':
        case 'R':
            if ( globalUtilOptind >= argc ) goto usage;
            Value = strtol( argv[globalUtilOptind], &pEnd, 10 );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || Value < 0 || Value > 1000 ) goto usage;
            globalUtilOptind++;
            if ( c == 'K' )
            {
                if ( Value < 2 || Value > 6 ) goto usage;
                pPars->nLutSize = (int)Value;
            }
            else if ( c == 'C' )
            {
                if ( Value < 2 || Value > pPars->nCutNumMax ) goto usage;
                pPars->nCutNum = (int)Value;
            }
            else if ( c == 'F' ) { if ( Value < 1 ) goto usage; pPars->nRounds = (int)Value; }
            else if ( c == 'A' ) pPars->nRoundsEla = (int)Value;
            else nRecover = (int)Value;
            break;
        case 'D':
            if ( globalUtilOptind >= argc ) goto usage;
            Delay = strtod( argv[globalUtilOptind], &pEnd );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || !(Delay >= 1.0/SCL_NUM && Delay < (double)SCL_INFINITY/SCL_NUM) ) goto usage;
            globalUtilOptind++;
            pPars->MapDelayTarget = (int)(Delay * SCL_NUM);
            break;
        case 'a': pPars->fAreaOnly ^= 1; break;
        case 's': fSynthesis ^= 1; break;
        case 'v': pPars->fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( Abc_FrameReadLibGen() == NULL )
    {
        Abc_Print( -1, "Current library is not available.\n" );
        return 1;
    }
    pNew = Nf3_ManPerformMapping( pAbc->pGia, pPars, fSynthesis, nRecover );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Nf3(): standard-cell mapping has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &nf3 [-KCFAR num] [-D float] [-asvh]\n" );
    Abc_Print( -2, "\t           performs standard-cell mapping with structural area recovery\n" );
    Abc_Print( -2, "\t-K num   : the maximum cut size (2 <= num <= 6) [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the maximum retained cuts (2 <= num <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : maximum delay and area flow rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-A num   : maximum exact area recovery rounds [default = %d]\n", pPars->nRoundsEla );
    Abc_Print( -2, "\t-R num   : cell recovery rounds (2+ allow two-cell decompositions) [default = %d]\n", nRecover );
    Abc_Print( -2, "\t-D float : sets the mapping delay constraint [default = best found]\n" );
    Abc_Print( -2, "\t-a       : toggles area-only mapping (ignores delay constraints) [default = %s]\n", pPars->fAreaOnly ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggles construction-proved synthesis choices [default = %s]\n", fSynthesis ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs the reference standard-cell mapper.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Nf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Nf_ManSetDefaultPars( Jf_Par_t * pPars );
    extern Gia_Man_t * Nf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars );
    extern Gia_Man_t * Pf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars );
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Nf_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFARLEDQMWZakpqfvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 2 || pPars->nLutSize > pPars->nLutSizeMax )
            {
                Abc_Print( -1, "LUT size %d is not supported.\n", pPars->nLutSize );
                goto usage;
            }
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutNum < 1 || pPars->nCutNum > pPars->nCutNumMax )
            {
                Abc_Print( -1, "This number of cuts (%d) is not supported.\n", pPars->nCutNum );
                goto usage;
            }
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nRoundsEla = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRoundsEla < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-R\" should be followed by an integer number.\n" );
                return 0;
            }
            pPars->nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRelaxRatio < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-R\" should be followed by an integer number.\n" );
                return 0;
            }
            pPars->nCoarseLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCoarseLimit < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-E\" should be followed by an integer number.\n" );
                return 0;
            }
            pPars->nAreaTuner = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaTuner < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer number.\n" );
                goto usage;
            }
            pPars->nReqTimeFlex = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nReqTimeFlex < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer number.\n" );
                goto usage;
            }
            pPars->nMaxMatches = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxMatches < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nVerbLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVerbLimit < 0 )
                goto usage;
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by an output file name.\n" );
                goto usage;
            }
            pPars->ZFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'p':
            pPars->fPinPerm ^= 1;
            break;
        case 'q':
            pPars->fPinQuick ^= 1;
            break;
        case 'f':
            pPars->fPinFilter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
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
    if ( Abc_FrameReadLibGen() == NULL )
    {
        Abc_Print( -1, "Current library is not available.\n" );
        return 1;
    }
//    if ( pPars->fAreaOnly )
//        pNew = Pf_ManPerformMapping( pAbc->pGia, pPars );
//    else
        pNew = Nf_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Nf(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &nf [-KCFARLEDQM num] [-Z file] [-akpqfvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n",                  pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n",           pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : the number of area flow rounds [default = %d]\n",                           pPars->nRounds );
    Abc_Print( -2, "\t-A num   : the number of exact area rounds (when \'-a\' is used) [default = %d]\n",    pPars->nRoundsEla );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n",                    pPars->nRelaxRatio );
    Abc_Print( -2, "\t-L num   : the fanout limit for coarsening XOR/MUX (num >= 2) [default = %d]\n",       pPars->nCoarseLimit );
    Abc_Print( -2, "\t-E num   : the area/edge tradeoff parameter (0 <= num <= 100) [default = %d]\n",       pPars->nAreaTuner );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n",                Buffer );
    Abc_Print( -2, "\t-Q num   : internal parameter impacting area of the mapping [default = %d]\n",         pPars->nReqTimeFlex );
    Abc_Print( -2, "\t-M num   : the max number of matches to dump into a binary file [default = %d]\n",     pPars->nMaxMatches );
    Abc_Print( -2, "\t-Z file  : the output file name to dump internal match info [default = unused]\n" );
    Abc_Print( -2, "\t-a       : toggles SAT-based area-oriented mapping (experimental) [default = %s]\n",   pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n",                     pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggles pin permutation (more matches - better quality) [default = %s]\n",  pPars->fPinPerm? "yes": "no" );
    Abc_Print( -2, "\t-q       : toggles quick mapping (fewer matches - worse quality) [default = %s]\n",    pPars->fPinQuick? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggles filtering matches (useful with unit delay model) [default = %s]\n", pPars->fPinFilter? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n",                                   pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n",                              pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Simap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Mio_IntallSimpleLibrary();
    extern int Gia_ManSimpleMapping( Gia_Man_t * p, int nBound, int Seed, int nBTLimit, int nTimeout, int fVerbose, int fKeepFile, int argc, char ** argv );
    int c, Seed = 0, nBTLimit = 0, nBound = 0, nTimeout = 0, fKeepFile = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BRCTfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nBound = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBound < 0 )
            {
                Abc_Print( -1, "Bound on a solution should be a positive integer.\n" );
                goto usage;
            }
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
            {
                Abc_Print( -1, "Conflict limit should be a positive integer.\n" );
                goto usage;
            }
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;            
        case 'f':
            fKeepFile ^= 1;
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
    Mio_IntallSimpleLibrary();
    if ( !Gia_ManSimpleMapping( pAbc->pGia, nBound, Seed, nBTLimit, nTimeout, fVerbose, fKeepFile, argc, argv ) )
        printf( "Simple mapping has failed.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: &simap [-BRCT num] [-fvh]\n" );
    Abc_Print( -2, "\t           performs simple mapping of the AIG\n" );
    Abc_Print( -2, "\t-B num   : the bound on the solution size [default = %d]\n", nBound );
    Abc_Print( -2, "\t-R num   : random number generator seed [default = %d]\n", Seed );
    Abc_Print( -2, "\t-C num   : the conflict limit [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-T num   : runtime limit in seconds [default = %d]\n", nTimeout );    
    Abc_Print( -2, "\t-f       : toggles keeping the intermediate CNF file [default = %s]\n", fKeepFile? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
