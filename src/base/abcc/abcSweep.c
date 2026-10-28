/**CFile****************************************************************

  FileName    [abcSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Equivalence reduction and choices.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "proof/fraig/fraig.h"
#include "proof/dch/dch.h"
#include "proof/cec/cec.h"
#include "proof/ssc/ssc.h"
#include "bool/lms/lms.h"
#include "opt/dar/dar.h"
#include "proof/abs/abs.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandSpeedup                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDChoice                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDch                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIFraig                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDFraig                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCSweep                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraig                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigTrust             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigStore             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigRestore           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigClean             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigSweep             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDumpEquiv              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecStart3              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecCollect3            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecGen3                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLmsTarget              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecEmbed3              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecFilter3             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecStop3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecPs3                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecAdd3                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecDump3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecMerge3              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SpecI              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv3             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Semi               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Choice             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Fraig              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9CFraig             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Srm                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Srm2               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Filter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Reduce             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9EquivMark          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9EquivFilter        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sweep              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Speedup            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dch                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dch2               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Rpm                ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers equivalence reduction and choices commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitSweep( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "speedup",       Abc_CommandSpeedup,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dchoice",       Abc_CommandDChoice,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dch",           Abc_CommandDch,              1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "ifraig",        Abc_CommandIFraig,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dfraig",        Abc_CommandDFraig,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "csweep",        Abc_CommandCSweep,           1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig",         Abc_CommandFraig,            1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_trust",   Abc_CommandFraigTrust,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_store",   Abc_CommandFraigStore,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_restore", Abc_CommandFraigRestore,     1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_clean",   Abc_CommandFraigClean,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_sweep",   Abc_CommandFraigSweep,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "dump_equiv",    Abc_CommandDumpEquiv,        0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_start3",    Abc_CommandRecStart3,        0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_collect3",  Abc_CommandRecCollect3,      0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_gen3",      Abc_CommandRecGen3,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lms",          Abc_CommandLmsTarget,        0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_embed3",    Abc_CommandRecEmbed3,        0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_filter3",   Abc_CommandRecFilter3,       0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_stop3",     Abc_CommandRecStop3,         0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_ps3",       Abc_CommandRecPs3,           0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_add3",      Abc_CommandRecAdd3,          0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_dump3",     Abc_CommandRecDump3,         0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_merge3",    Abc_CommandRecMerge3,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&speci",        Abc_CommandAbc9SpecI,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv",        Abc_CommandAbc9Equiv,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv2",       Abc_CommandAbc9Equiv2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv3",       Abc_CommandAbc9Equiv3,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&semi",         Abc_CommandAbc9Semi,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&choice",       Abc_CommandAbc9Choice,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&fraig",        Abc_CommandAbc9Fraig,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cfraig",       Abc_CommandAbc9CFraig,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&srm",          Abc_CommandAbc9Srm,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&srm2",         Abc_CommandAbc9Srm2,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&filter",       Abc_CommandAbc9Filter,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reduce",       Abc_CommandAbc9Reduce,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv_mark",   Abc_CommandAbc9EquivMark,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv_filter", Abc_CommandAbc9EquivFilter,  0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sweep",        Abc_CommandAbc9Sweep,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&speedup",      Abc_CommandAbc9Speedup,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dch",          Abc_CommandAbc9Dch,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dch2",         Abc_CommandAbc9Dch2,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&rpm",          Abc_CommandAbc9Rpm,          0 );
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
int Abc_CommandSpeedup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int fVeryVerbose;
    extern Abc_Ntk_t * Abc_NtkSpeedup( Abc_Ntk_t * pNtk, int fUseLutLib, int Percentage, int Degree, int fVerbose, int fVeryVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fUseLutLib = 0;
    Percentage = 5;
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
    pNtkRes = Abc_NtkSpeedup( pNtk, fUseLutLib, Percentage, Degree, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: speedup [-PN <num>] [-lvwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to speedup the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : delay delta defining critical path for library model [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
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
int Abc_CommandDChoice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, fUpdateLevel, fConstruct, c;
    int nConfMax, nLevelMax;

    extern Abc_Ntk_t * Abc_NtkDChoice( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fConstruct, int nConfMax, int nLevelMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance     = 1;
    fUpdateLevel = 1;
    fConstruct   = 0;
    nConfMax     = 1000;
    nLevelMax    = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CLblcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 )
                goto usage;
            break;
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
        case 'b':
            fBalance ^= 1;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'c':
            fConstruct ^= 1;
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
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDChoice( pNtk, fBalance, fUpdateLevel, fConstruct, nConfMax, nLevelMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dchoice [-C num] [-L num] [-blcvh]\n" );
    Abc_Print( -2, "\t         performs partitioned choicing using new AIG package\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-L num : the max level of nodes to consider (0 = not used) [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle updating level [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle constructive computation of choices [default = %s]\n", fConstruct? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Dch_Pars_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkDch( Abc_Ntk_t * pNtk, Dch_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dch_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCSsptgcfrxvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 )
                goto usage;
            break;
        case 's':
            pPars->fSynthesis ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 't':
            pPars->fSimulateTfo ^= 1;
            break;
        case 'g':
            pPars->fUseGia ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'f':
            pPars->fLightSynth ^= 1;
            break;
        case 'r':
            pPars->fSkipRedSupp ^= 1;
            break;
        case 'x':
            pPars->fUseNew ^= 1;
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
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDch( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dch [-WCS num] [-sptgcfrxvh]\n" );
    Abc_Print( -2, "\t         computes structural choices using a new approach\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-s     : toggle synthesizing three snapshots [default = %s]\n", pPars->fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle simulation of the TFO classes [default = %s]\n", pPars->fSimulateTfo? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using GIA to prove equivalences [default = %s]\n", pPars->fUseGia? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT vs. MiniSat [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle using faster logic synthesis [default = %s]\n", pPars->fLightSynth? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle skipping choices with redundant support [default = %s]\n", pPars->fSkipRedSupp? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle using new choice computation [default = %s]\n", pPars->fUseNew? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fProve, fVerbose, fDoSparse;
    int nConfLimit;
    int nPartSize;
    int nLevelMax;

    extern Abc_Ntk_t * Abc_NtkIvyFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarFraigPart( Abc_Ntk_t * pNtk, int nPartSize, int nConfLimit, int nLevelMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nPartSize    = 0;
    nLevelMax    = 0;
    nConfLimit   = 100;
    fDoSparse    = 1;
    fProve       = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PCLspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 )
                goto usage;
            break;
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
        case 's':
            fDoSparse ^= 1;
            break;
        case 'p':
            fProve ^= 1;
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
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    if ( nPartSize > 0 )
        pNtkRes = Abc_NtkDarFraigPart( pNtk, nPartSize, nConfLimit, nLevelMax, fVerbose );
    else
        pNtkRes = Abc_NtkIvyFraig( pNtk, nConfLimit, fDoSparse, fProve, 0, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: ifraig [-P num] [-C num] [-L num] [-spvh]\n" );
    Abc_Print( -2, "\t         performs fraiging using a new method\n" );
    Abc_Print( -2, "\t-P num : partition size (0 = partitioning is not used) [default = %d]\n", nPartSize );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-L num : limit on node level to fraig (0 = fraig all nodes) [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n", fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n", fProve? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nConfLimit, fDoSparse, fProve, fSpeculate, fChoicing, fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fSpeculate, int fChoicing, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nConfLimit   = 100;
    fDoSparse    = 1;
    fProve       = 0;
    fSpeculate   = 0;
    fChoicing    = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Csprcvh" ) ) != EOF )
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
        case 's':
            fDoSparse ^= 1;
            break;
        case 'p':
            fProve ^= 1;
            break;
        case 'r':
            fSpeculate ^= 1;
            break;
        case 'c':
            fChoicing ^= 1;
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
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDarFraig( pNtk, nConfLimit, fDoSparse, fProve, 0, fSpeculate, fChoicing, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dfraig [-C num] [-sprcvh]\n" );
    Abc_Print( -2, "\t         performs fraiging using a new method\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n", fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n", fProve? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle speculative reduction [default = %s]\n", fSpeculate? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle accumulation of choices [default = %s]\n", fChoicing? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nCutsMax, nLeafMax, fVerbose;

    extern Abc_Ntk_t * Abc_NtkCSweep( Abc_Ntk_t * pNtk, int nCutsMax, int nLeafMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nCutsMax  =  8;
    nLeafMax  =  6;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CKvh" ) ) != EOF )
    {
        switch ( c )
        {
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

    if ( nCutsMax < 2 )
    {
        Abc_Print( -1, "The number of cuts cannot be less than 2.\n" );
        return 1;
    }

    if ( nLeafMax < 3 || nLeafMax > 16 )
    {
        Abc_Print( -1, "The number of leaves is infeasible.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkCSweep( pNtk, nCutsMax, nLeafMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: csweep [-C num] [-K num] [-vh]\n" );
    Abc_Print( -2, "\t         performs cut sweeping using a new method\n" );
    Abc_Print( -2, "\t-C num : limit on the number of cuts (C >= 2) [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-K num : limit on the cut size (3 <= K <= 16) [default = %d]\n", nLeafMax );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Fraig_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fAllNodes;
    int fExdc;
    int c;
    int fPartition = 0;
    extern void Abc_NtkFraigPartitionedTime( Abc_Ntk_t * pNtk, void * pParams );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fExdc     = 0;
    fAllNodes = 0;
    memset( pParams, 0, sizeof(Fraig_Params_t) );
    pParams->nPatsRand  = 2048; // the number of words of random simulation info
    pParams->nPatsDyna  = 2048; // the number of words of dynamic simulation info
    pParams->nBTLimit   =  100; // the max number of backtracks to perform
    pParams->fFuncRed   =    1; // performs only one level hashing
    pParams->fFeedBack  =    1; // enables solver feedback
    pParams->fDist1Pats =    1; // enables distance-1 patterns
    pParams->fDoSparse  =    1; // performs equiv tests for sparse functions
    pParams->fChoicing  =    0; // enables recording structural choices
    pParams->fTryProve  =    0; // tries to solve the final miter
    pParams->fVerbose   =    0; // the verbosiness flag
    pParams->fVerboseP  =    0; // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "RDCrscptvaeh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsRand = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nPatsRand < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsDyna = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nPatsDyna < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nBTLimit < 0 )
                goto usage;
            break;

        case 'r':
            pParams->fFuncRed ^= 1;
            break;
        case 's':
            pParams->fDoSparse ^= 1;
            break;
        case 'c':
            pParams->fChoicing ^= 1;
            break;
        case 'p':
            pParams->fTryProve ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 't':
            fPartition ^= 1;
            break;
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'e':
            fExdc ^= 1;
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
        Abc_Print( -1, "Can only fraig a logic network or an AIG.\n" );
        return 1;
    }

    // report the proof
    pParams->fVerboseP = pParams->fTryProve;

    // get the new network
    if ( fPartition )
    {
        pNtkRes = Abc_NtkDup( pNtk );
        if ( Abc_NtkIsStrash(pNtk) )
            Abc_NtkFraigPartitionedTime( pNtk, &Params );
        else
        {
            pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes, 0 );
            Abc_NtkFraigPartitionedTime( pNtk, &Params );
            Abc_NtkDelete( pNtk );
        }
    }
    else
    {
        if ( Abc_NtkIsStrash(pNtk) )
            pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
        else
        {
            pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes, 0 );
            pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
            Abc_NtkDelete( pNtk );
        }
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraiging has failed.\n" );
        return 1;
    }

    if ( pParams->fTryProve ) // report the result
        Abc_NtkMiterReport( pNtkRes );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    sprintf(Buffer, "%d", pParams->nBTLimit );
    Abc_Print( -2, "usage: fraig [-R num] [-D num] [-C num] [-rscpvtah]\n" );
    Abc_Print( -2, "\t         transforms a logic network into a functionally reduced AIG\n" );
    Abc_Print( -2, "\t         (known bugs: takes an UNSAT miter and returns a SAT one)\n");
    Abc_Print( -2, "\t         (there are newer fraiging commands, \"ifraig\" and \"dfraig\")\n" );
    Abc_Print( -2, "\t-R num : number of random patterns (127 < num < 32769) [default = %d]\n",     pParams->nPatsRand );
    Abc_Print( -2, "\t-D num : number of systematic patterns (127 < num < 32769) [default = %d]\n", pParams->nPatsDyna );
    Abc_Print( -2, "\t-C num : number of backtracks for one SAT problem [default = %s]\n",    pParams->nBTLimit==-1? "infinity" : Buffer );
    Abc_Print( -2, "\t-r     : toggle functional reduction [default = %s]\n",                 pParams->fFuncRed? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n",         pParams->fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle accumulation of choices [default = %s]\n",              pParams->fChoicing? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n",              pParams->fTryProve? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n",                       pParams->fVerbose?  "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle functional sweeping using EXDC [default = %s]\n",       fExdc? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle between all nodes and DFS nodes [default = %s]\n",      fAllNodes? "all": "dfs" );
    Abc_Print( -2, "\t-t     : toggle using partitioned representation [default = %s]\n",     fPartition? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigTrust( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
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
    pNtkRes = Abc_NtkFraigTrust( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraiging in the trust mode has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_trust [-h]\n" );
    Abc_Print( -2, "\t        transforms the current network into an AIG assuming it is FRAIG with choices\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigStore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fDuplicate;

    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
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
    if ( !Abc_NtkFraigStore( pNtk ) )
    {
        Abc_Print( -1, "Fraig storing has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_store [-h]\n" );
    Abc_Print( -2, "\t        saves the current network in the AIG database\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigRestore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nPatsRand  =    0;    // the number of words of random simulation info
    int nPatsDyna  =    0;    // the number of words of dynamic simulation info
    int nBTLimit   = 1000;    // the max number of backtracks to perform

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "RDCh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nPatsRand = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPatsRand < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nPatsDyna = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPatsDyna < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
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

    // get the new network
    pNtkRes = Abc_NtkFraigRestore( nPatsRand, nPatsDyna, nBTLimit );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraig restoring has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_restore [-RDC num] [-h]\n" );
    Abc_Print( -2, "\t         makes the current network by fraiging the AIG database\n" );
    Abc_Print( -2, "\t-R num : number of random patterns (127 < num < 32769) [default = design-dependent]\n" );
    Abc_Print( -2, "\t-D num : number of systematic patterns (127 < num < 32769) [default = design-dependent]\n" );
    Abc_Print( -2, "\t-C num : number of backtracks for one SAT problem [default = %d]\n",  nBTLimit );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigClean( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fDuplicate;
    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    Abc_NtkFraigStoreClean();
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_clean [-h]\n" );
    Abc_Print( -2, "\t        cleans the internal FRAIG storage\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseInv;
    int fExdc;
    int fVerbose;
    int fVeryVerbose;
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );
    // set defaults
    fUseInv   = 1;
    fExdc     = 0;
    fVerbose  = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ievwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fUseInv ^= 1;
            break;
        case 'e':
            fExdc ^= 1;
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
        Abc_Print( -1, "Cannot sweep AIGs (use \"fraig\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Transform the current network into a logic network.\n" );
        return 1;
    }
    // modify the current network
    if ( !Abc_NtkFraigSweep( pNtk, fUseInv, fExdc, fVerbose, fVeryVerbose ) )
    {
        Abc_Print( -1, "Sweeping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_sweep [-evwh]\n" );
    Abc_Print( -2, "\t        performs technology-dependent sweep\n" );
    Abc_Print( -2, "\t-e    : toggle functional sweeping using EXDC [default = %s]\n", fExdc? "yes": "no" );
    Abc_Print( -2, "\t-v    : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w    : prints equivalence class information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDumpEquiv( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkDumpEquiv( Abc_Ntk_t * pNtks[2], char * pFileName, int nConfs, int fByName, int fVerbose );
    Abc_Ntk_t * pNtks[2] = {NULL};
    char * pFileName[2], * pFileNameOut;
    int c, nConfs = 1000, fByName = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 )
                goto usage;
            break;
        case 'n':
            fByName ^= 1;
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
    if ( argc != globalUtilOptind + 3 )
    {
        Abc_Print( -1, "Expecting three file names on the command line.\n" );
        goto usage;
    }
    pFileName[0] = argv[globalUtilOptind];
    pFileName[1] = argv[globalUtilOptind+1];
    pFileNameOut = argv[globalUtilOptind+2];
    for ( c = 0; c < 2; c++ )
    {
        pNtks[c] = Io_Read( pFileName[c], Io_ReadFileType(pFileName[c]), 1, 0 );
        if ( pNtks[c] == NULL )
            goto usage;
        Abc_NtkToAig( pNtks[c] );
    }
//    if ( Abc_NtkCiNum(pNtks[0]) != Abc_NtkCiNum(pNtks[1]) )
//        Abc_Print( -1, "The number of primary inputs of networks \"%s\" and \"%s\" does not match.\n", Abc_NtkName(pNtks[0]), Abc_NtkName(pNtks[1]) );
//    else if ( Abc_NtkCoNum(pNtks[0]) != Abc_NtkCoNum(pNtks[1]) )
//        Abc_Print( -1, "The number of primary outputs of networks \"%s\" and \"%s\" does not match.\n", Abc_NtkName(pNtks[0]), Abc_NtkName(pNtks[1]) );
//    else
        Abc_NtkDumpEquiv( pNtks, pFileNameOut, nConfs, fByName, fVerbose );
    Abc_NtkDelete( pNtks[0] );
    Abc_NtkDelete( pNtks[1] );
    return 0;

usage:
    Abc_Print( -2, "usage: dump_equiv [-C num] [-nvh] <file1.blif> <file2.blif> <file_dump_equiv.txt>\n" );
    Abc_Print( -2, "\t          computes equivalence classes of nodes in <file1> and <file2>\n" );
    Abc_Print( -2, "\t          By default this procedure performs matching of primary inputs by name.\n" );
    Abc_Print( -2, "\t          Those inputs that cannot be matched are treated as free variables.\n" );
    Abc_Print( -2, "\t          There is no effort to match primary outputs. Indeed, if two outputs\n" );
    Abc_Print( -2, "\t          are equivalent, they will belong to the same equivalence class in the end.\n" );
    Abc_Print( -2, "\t-C num  : the maximum number of conflicts at each node [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-n      : enable matching of primary inputs by name [default = %s]\n", fByName? "yes": "no" );
    Abc_Print( -2, "\t-v      : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<file1> : first network whose nodes are considered\n" );
    Abc_Print( -2, "\t<file2> : second network whose nodes are considered\n" );
    Abc_Print( -2, "\t<file_dump_equiv> : text file with node equivalence classes\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecStart3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkRecXorMode3( void );
    char * FileName, * pTemp;
    char ** pArgvNew;
    int c, nArgcNew;
    FILE * pFile;
    Gia_Man_t * pGia = NULL;
    int nVars = 6;
    int nCuts = 32;
    int fFuncOnly = 0;
    int fXor = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCfxvh" ) ) != EOF )
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
            if ( nVars < 1 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCuts < 1 )
                goto usage;
            break;
        case 'f':
            fFuncOnly ^= 1;
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
    if ( !(nVars >= 3 && nVars <= 16) )
    {
        Abc_Print( -1, "The range of allowed values is 3 <= K <= 16.\n" );
        return 0;
    }
    if ( Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "The AIG subgraph recording is already started.\n" );
        return 0;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( fXor && (nArgcNew != 1 || fFuncOnly) )
    {
        Abc_Print(-1, "rec_start3 -x requires a structure-library file and is incompatible with -f.\n");
        return 1;
    }
    if ( nArgcNew != 1 )
        Abc_Print( 1, "File name is not given on the command line. Starting a new record.\n" );
    else
    {
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
        pGia = Gia_AigerRead( FileName, 0, 1, 0 );
        if ( pGia == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 0;
        }
    }
    Abc_NtkRecStart3( pGia, nVars, nCuts, fFuncOnly, fVerbose );
    if ( fXor ) Abc_NtkRecXorMode3();
    return 0;

usage:
    Abc_Print( -2, "usage: rec_start3 [-K num] [-C num] [-fxvh] <file>\n" );
    Abc_Print( -2, "\t         starts recording AIG subgraphs (should be called for\n" );
    Abc_Print( -2, "\t         an empty network or after reading in a previous record)\n" );
    Abc_Print( -2, "\t-K num : the largest number of inputs [default = %d]\n", nVars );
    Abc_Print( -2, "\t-C num : the max number of cuts used at a node (0 < num < 2^12) [default = %d]\n", nCuts );
    Abc_Print( -2, "\t-f     : toggles recording functions without AIG subgraphs [default = %s]\n", fFuncOnly? "yes": "no" );
    Abc_Print( -2, "\t-x     : count recognized three-AND XORs as one gate/level in LMS [default = no]\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : AIGER file with the library\n");
    Abc_Print( -2, "\t         loaded structure libraries use exact winner caching by default\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecStop3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "This command works only after calling \"rec_start3\".\n" );
        return 0;
    }
    Abc_NtkRecStop3();
    return 0;

usage:
    Abc_Print( -2, "usage: rec_stop3 [-h]\n" );
    Abc_Print( -2, "\t        cleans the internal storage for AIG subgraphs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandRecFilter3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_LmsFilterControl3( int Mode, FILE * pOut );
    int c, Mode = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "cdvh")) != EOF )
    {
        if ( c == 'd' && Mode == 1 ) Mode = 0;
        else if ( c == 'c' && Mode == 1 ) Mode = 3;
        else if ( c == 'v' && Mode == 1 ) Mode = 2;
        else goto usage;
    }
    if ( argc != globalUtilOptind ) goto usage;
    return Abc_LmsFilterControl3(Mode, Abc_FrameReadOut(pAbc));
usage:
    Abc_Print(-2, "usage: rec_filter3 [-c | -d | -v] [-h]\n");
    Abc_Print(-2, "       Enable exact late-input filtering for the loaded LMS library.\n");
    Abc_Print(-2, "       -d : disable filtering and caching (exact caching is on by default)\n");
    Abc_Print(-2, "       -c : enable filtering and an empty exact winning-structure cache\n");
    Abc_Print(-2, "       -v : print status and candidate statistics without changing mode\n");
    Abc_Print(-2, "       Enabling resets counters; cached indexes are retained.\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Controls recording of LMS synthesis examples.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandRecCollect3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_LmsCollectControl3( const char * pFileName, int Mode, FILE * pError );
    int c, Mode = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "rsh")) != EOF )
    {
        if ( c == 'r' && !Mode ) Mode = 1;
        else if ( c == 's' && !Mode ) Mode = 2;
        else goto usage;
    }
    if ( argc-globalUtilOptind != (Mode ? 0 : 1) ) goto usage;
    return Abc_LmsCollectControl3(Mode ? NULL : argv[globalUtilOptind], Mode, Abc_FrameReadErr(pAbc));
usage:
    Abc_Print(-2, "usage: rec_collect3 [-r | -s] <samples.txt>\n");
    Abc_Print(-2, "       Collect selected LMS functions and their input arrivals.\n");
    Abc_Print(-2, "       -r : start/reset sampling of the loaded six-input library\n");
    Abc_Print(-2, "       -s : stop sampling; without switches write accumulated samples\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Experimental target-delay LMS replacement selection.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandLmsTarget( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkRecStartBuiltin3( FILE *, FILE * );
    Gia_Man_t * pNew;
    int c, Pass, Target = -1, Cuts = 8, CriticalCuts = 0, Rounds = 4, Exact = 16, Passes = 1, DpMode = 2, Memory = 1024, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "DCBIEPLMvh")) != EOF )
    {
        if ( c == 'v' ) fVerbose ^= 1;
        else if ( c == 'D' || c == 'C' || c == 'B' || c == 'I' || c == 'E' || c == 'P' || c == 'L' || c == 'M' )
        {
            char * pEnd, * pStart;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            pStart = argv[globalUtilOptind++];
            Value = strtol(pStart, &pEnd, 10);
            if ( pStart == pEnd || *pEnd || Value < (c == 'D' ? -1 : c == 'B' || c == 'E' || c == 'L' || c == 'M' ? 0 : 1) || Value > (c == 'D' ? 100000 : c == 'C' || c == 'B' ? 128 : c == 'E' ? 256 : c == 'L' ? 2 : c == 'M' ? 1048576 : 100) ) goto usage;
            if ( c == 'D' ) Target = (int)Value;
            if ( c == 'C' ) Cuts = (int)Value;
            if ( c == 'B' ) CriticalCuts = (int)Value;
            if ( c == 'I' ) Rounds = (int)Value;
            if ( c == 'E' ) Exact = (int)Value;
            if ( c == 'P' ) Passes = (int)Value;
            if ( c == 'L' ) DpMode = (int)Value;
            if ( c == 'M' ) Memory = (int)Value;
        }
        else goto usage;
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( !pAbc->pGia ) { Abc_Print(-1, "There is no AIG.\n"); return 1; }
    if ( !Abc_NtkRecIsRunning3() && !Abc_NtkRecStartBuiltin3(Abc_FrameReadOut(pAbc), Abc_FrameReadErr(pAbc)) ) return 1;
    pNew = Lms_TargetPerformAdaptive(pAbc->pGia, Target, Cuts, Rounds, Exact, DpMode, Memory, CriticalCuts, fVerbose);
    if ( !pNew ) return 1;
    // Preserve given output requirements across passes. Without them,
    // freeze the first pass's achieved arrival, including late CIs.
    if ( Target < 0 && !pNew->vCoReqs )
        Target = pNew->vCoArrs && Vec_IntSize(pNew->vCoArrs) ? Vec_IntFindMax(pNew->vCoArrs) : Gia_ManLevelNum(pNew);
    // Recollect on the rewritten AIG, exposing new macro interiors and cut
    // boundaries. Keep the deadline DP on each pass; do not freeze the input.
    for ( Pass = 1; Pass < Passes; ++Pass )
    {
        Gia_Man_t * pTrial;
        if ( fVerbose ) Abc_Print(1, "LMS target: recollection pass %d of %d.\n", Pass+1, Passes);
        pTrial = Lms_TargetPerformAdaptive(pNew, Target, Cuts, Rounds, Exact, DpMode, Memory, CriticalCuts, fVerbose);
        if ( !pTrial )
        {
            Abc_Print(0, "LMS target: recollection failed; keeping the preceding feasible result.\n");
            break;
        }
        if ( Gia_ManAndNum(pTrial) >= Gia_ManAndNum(pNew) )
        {
            Gia_ManStop(pTrial);
            if ( fVerbose ) Abc_Print(1, "LMS target: no area improvement; stopping recollection.\n");
            break;
        }
        Gia_ManStop(pNew);
        pNew = pTrial;
    }
    Abc_FrameUpdateGia(pAbc, pNew);
    return 0;
usage:
    Abc_Print(-2, "usage: &lms [-D num] [-CBIEPLM num] [-vh]\n");
    Abc_Print(-2, "           experimental LMS-inspired delay-optimization\n");
    Abc_Print(-2, "\t-D num : maximum output arrival (unit AND delay); -1 = automatic\n");
    Abc_Print(-2, "\t         default: given CO requirements, or best arrival in the cut bank\n");
    Abc_Print(-2, "\t         honors GIA integer CI arrivals/CO requirements; explicit -D caps every CO\n");
    Abc_Print(-2, "\t-C num : retained cuts per node [default = %d]\n", Cuts);
    Abc_Print(-2, "\t-B num : recollect zero-slack macros with this cut budget; 0 = disabled [default = %d]\n", CriticalCuts);
    Abc_Print(-2, "\t         must exceed -C to add a pilot-guided collection (maximum 128)\n");
    Abc_Print(-2, "\t-I num : sharing-estimate rounds [default = %d]\n", Rounds);
    Abc_Print(-2, "\t-E num : ranked exact-area trials per root; 0 = exhaustive [default = %d]\n", Exact);
    Abc_Print(-2, "\t-P num : maximum collect/select passes; stop without area gain [default = %d]\n", Passes);
    Abc_Print(-2, "\t-L num : deadline DP: 0 = dense, 1 = lazy, 2 = adaptive [default = %d]\n", DpMode);
    Abc_Print(-2, "\t-M num : deadline-table budget in MiB; 0 = unlimited [default = %d]\n", Memory);
    Abc_Print(-2, "\t         limits extra deadline slack when needed; preserves feasibility but may restrict area search\n");
    Abc_Print(-2, "\t-v     : print timing, memory, and optimization statistics\n");
    Abc_Print(-2, "\t-h     : print usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Generates an LMS library from recorded examples.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandRecGen3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fXor = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "xh")) != EOF )
        if ( c == 'x' ) fXor ^= 1;
        else goto usage;
    if ( argc-globalUtilOptind != 2 ) goto usage;
    return !(fXor ? Lms_LibGenerateXor(argv[globalUtilOptind], argv[globalUtilOptind+1], Abc_FrameReadErr(pAbc)) :
                   Lms_LibGenerate(argv[globalUtilOptind], argv[globalUtilOptind+1], Abc_FrameReadErr(pAbc)));
usage:
    Abc_Print(-2, "usage: rec_gen3 [-x] <samples.txt> <library.aig>\n");
    Abc_Print(-2, "       Generate a six-input LMS library from truth/arrival samples.\n");
    Abc_Print(-2, "       Canonicalize, deduplicate, and retain area/pin-depth alternatives.\n");
    Abc_Print(-2, "       The output must be a new file. No recorded library is required.\n");
    Abc_Print(-2, "       -x : generate unit AND/XOR profiles, written as three-AND XOR patterns\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Embeds an LMS library.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CommandRecEmbed3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fDecode = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "dh")) != EOF )
        if ( c == 'd' ) fDecode ^= 1;
        else goto usage;
    if ( argc-globalUtilOptind != (fDecode ? 1 : 2) ) goto usage;
    return !(fDecode ? Lms_BuiltinWrite(argv[globalUtilOptind], Abc_FrameReadErr(pAbc)) :
        Lms_EmbedWrite(argv[globalUtilOptind], argv[globalUtilOptind+1], Abc_FrameReadErr(pAbc)));
usage:
    Abc_Print(-2, "usage: rec_embed3 [-h] <library.aig> <data.inc>\n");
    Abc_Print(-2, "       Encode a six-input LMS library as a compact C initializer.\n");
    Abc_Print(-2, "       rec_embed3 -d <library.aig> decodes the compiled-in initializer.\n");
    Abc_Print(-2, "       Output must be a new file. The active LMS manager is unchanged.\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints LMS library statistics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecPs3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fPrintLib = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'p':
            fPrintLib ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "No LMS library is active (use \"rec_start3\" or \"&if -y\").\n" );
        return 0;
    }
    Abc_NtkRecPs3(fPrintLib);
    return 0;

usage:
    Abc_Print( -2, "usage: rec_ps3 [-h]\n" );
    Abc_Print( -2, "\t        prints statistics about the recorded AIG subgraphs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecAdd3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseSOPB = 0;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "gh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'g':
            fUseSOPB = 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works for AIGs.\n" );
        return 0;
    }
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "This command works for AIGs after calling \"rec_start3\".\n" );
        return 0;
    }
    Abc_NtkRecAdd3( pNtk, fUseSOPB );
    return 0;

usage:
    Abc_Print( -2, "usage: rec_add3 [-h]\n" );
    Abc_Print( -2, "\t        adds subgraphs from the current network to the set\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecDump3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkRecDumpTt3( char * pFileName, int fBinary );
    char * FileName;
    char ** pArgvNew;
    int nArgcNew;
    Gia_Man_t * pGia;
    int fAscii = 0;
    int fBinary = 0;
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "abh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAscii ^= 1;
            break;
        case 'b':
            fBinary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "The AIG subgraph recording is not started.\n" );
        return 1;
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
    if ( fAscii )
        Abc_NtkRecDumpTt3( FileName, 0 );
    else if ( fBinary )
        Abc_NtkRecDumpTt3( FileName, 1 );
    else
    {
        pGia = Abc_NtkRecGetGia3();
        if( pGia == NULL )
        {
            Abc_Print( 0, "Library AIG is not available.\n" );
            return 1;
        }
        if( Gia_ManPoNum(pGia) == 0 )
        {
            Abc_Print( 0, "No structure in the library.\n" );
            return 1;
        }
        Gia_AigerWrite( pGia, FileName, 0, 0, 0 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: rec_dump3 [-abh] <file>\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-a     : toggles dumping TTs into an ASCII file [default = %s]\n", fAscii? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles dumping TTs into a binary file [default = %s]\n", fBinary? "yes": "no" );
    Abc_Print( -2, "\t<file> : AIGER file to write the library\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecMerge3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    char * FileName, * pTemp;
    char ** pArgvNew;
    int nArgcNew;
    FILE * pFile;
    Gia_Man_t * pGia = NULL;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "This command works for AIGs only after calling \"rec_start3\".\n" );
        return 0;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    else
    {
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
        pGia = Gia_AigerRead( FileName, 0, 1, 0 );
        if ( pGia == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 0;
        }
    }
    Abc_NtkRecLibMerge3(pGia);
    Gia_ManStop( pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: rec_merge3 [-h] <file>\n" );
    Abc_Print( -2, "\t         merge libraries\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : AIGER file with the library\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SpecI( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_CommandSpecI( Gia_Man_t * pGia, int nFrames, int nBTLimit, int fUseStart, int fCheckMiter, int fVerbose );
    int nFrames     =   100;
    int nBTLimit    = 25000;
    int fUseStart   =     1;
    int fCheckMiter =     1;
    int fVerbose    =     0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCfmvh" ) ) != EOF )
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
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
                goto usage;
            break;
        case 'f':
            fUseStart ^= 1;
            break;
        case 'm':
            fCheckMiter ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9SpecI(): There is no AIG.\n" );
        return 1;
    }
    Gia_CommandSpecI( pAbc->pGia, nFrames, nBTLimit, fUseStart, fCheckMiter, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &speci [-FC num] [-fmvh]\n" );
    Abc_Print( -2, "\t         refines equivalence classes using speculative reduction\n" );
    Abc_Print( -2, "\t-F num : the max number of time frames [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-f     : toggle starting BMC from a later frame [default = %s]\n", fUseStart? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", fCheckMiter? "miter": "circuit" );
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
int Abc_CommandAbc9Equiv( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSim_t Pars, * pPars = &Pars;
    int c;
    Cec_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFRSTsmdvh" ) ) != EOF )
    {
        switch ( c )
        {
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
            pPars->nNonRefines = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNonRefines < 0 )
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
        case 's':
            pPars->fSeqSimulate ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Equiv(): There is no AIG.\n" );
        return 1;
    }
    Cec_ManSimulation( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv [-WFRST num] [-smdvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-R num : the max number of simulation rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-S num : the max number of rounds w/o refinement to stop [default = %d]\n", pPars->nNonRefines );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-s     : toggle seq vs. comb simulation [default = %s]\n", pPars->fSeqSimulate? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using two POs instead of XOR [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Equiv2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Ssw_SignalFilterGia( Gia_Man_t * p, int nFramesMax, int nConfMax, int nRounds, int TimeLimit, int TimeLimit2, Abc_Cex_t * pCex, int fLatchOnly, int fVerbose );
    int nFramesMax =   20;
    int nConfMax   =  500;
    int nRounds    =   10;
    int TimeLimit  =    0;
    int TimeLimit2 =    0;
    int fUseCex    =    0;
    int fLatchOnly =    0;
    int fVerbose   =    0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCRTSxlvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 )
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeLimit2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeLimit2 < 0 )
                goto usage;
            break;
        case 'x':
            fUseCex ^= 1;
            break;
        case 'l':
            fLatchOnly ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Equiv2(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "Abc_CommandAbc9Equiv2(): There is no flops. Nothing is done.\n" );
        return 0;
    }
    if ( fUseCex )
    {
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv2(): Counter-example is not available.\n" );
            return 0;
        }
        if ( pAbc->pCex->nPis != Gia_ManPiNum(pAbc->pGia) )
        {
            Abc_Print( -1, "Abc_CommandAbc9Equiv2(): The number of PIs differs in cex (%d) and in AIG (%d).\n",
                pAbc->pCex->nPis, Gia_ManPiNum(pAbc->pGia) );
            return 1;
        }
    }
    Ssw_SignalFilterGia( pAbc->pGia, nFramesMax, nConfMax, nRounds, TimeLimit, TimeLimit2, fUseCex? pAbc->pCex: NULL, fLatchOnly, fVerbose );
    pAbc->Status  = -1;
//    pAbc->nFrames = pAbc->pCex->iFrame;
//    Abc_FrameReplaceCex( pAbc, &pAbc->pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv2 [-FCRTS num] [-xlvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-F num : the max number of frames for BMC [default = %d]\n", nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-R num : the max number of BMC rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-T num : runtime limit in seconds for all rounds [default = %d]\n", TimeLimit );
    Abc_Print( -2, "\t-S num : runtime limit in seconds for one round [default = %d]\n", TimeLimit2 );
    Abc_Print( -2, "\t-x     : toggle using the current cex to perform refinement [default = %s]\n", fUseCex? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle considering only latch output equivalences [default = %s]\n", fLatchOnly? "yes": "no" );
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
int Abc_CommandAbc9Equiv3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Ssw_RarSignalFilterGia( Gia_Man_t * p, Ssw_RarPars_t * pPars );
    Ssw_RarPars_t Pars, * pPars = &Pars;
    int c;
    Ssw_RarSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRSNTmxlvh" ) ) != EOF )
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
        case 'm':
            pPars->fMiter ^= 1;
            break;
        case 'x':
            pPars->fUseCex ^= 1;
            break;
        case 'l':
            pPars->fLatchOnly ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Equiv3(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "Abc_CommandAbc9Equiv3(): There is no flops. Nothing is done.\n" );
        return 0;
    }
    if ( pPars->fUseCex )
    {
        if ( pPars->fMiter )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv3(): Considering the miter as a circuit because the CEX is given.\n" );
            pPars->fMiter = 0;
        }
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv3(): Counter-example is not available.\n" );
            return 0;
        }
        if ( pAbc->pCex->nPis != Gia_ManPiNum(pAbc->pGia) )
        {
            Abc_Print( -1, "Abc_CommandAbc9Equiv3(): The number of PIs differs in cex (%d) and in AIG (%d).\n",
                pAbc->pCex->nPis, Gia_ManPiNum(pAbc->pGia) );
            return 1;
        }
        pPars->pCex = pAbc->pCex;
    }
    pAbc->Status = Ssw_RarSignalFilterGia( pAbc->pGia, pPars );
//    pAbc->nFrames = pAbc->pGia->pCexSeq->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv3 [-FWRSNT num] [-mxlvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-F num : the max number of frames for BMC [default = %d]\n",                   pPars->nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",                    pPars->nWords );
    Abc_Print( -2, "\t-R num : the max number of simulation rounds [default = %d]\n",                pPars->nRounds );
    Abc_Print( -2, "\t-S num : the number of rounds before a restart [default = %d]\n",              pPars->nRestart );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n",              pPars->nRandSeed );
    Abc_Print( -2, "\t-T num : runtime limit in seconds for all rounds [default = %d]\n",            pPars->TimeOut );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n",                       pPars->fMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-x     : toggle using the current CEX to perform refinement [default = %s]\n", pPars->fUseCex? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle considering only latch output equivalences [default = %s]\n",  pPars->fLatchOnly? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",                pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Semi( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSmf_t Pars, * pPars = &Pars;
    int c;
    Cec_ManSmfSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WRFSMCTmdvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNonRefines = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNonRefines < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMinOutputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMinOutputs < 0 )
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
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
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
    Cec_ManSeqSemiformal( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &semi [-WRFSMCT num] [-mdvh]\n" );
    Abc_Print( -2, "\t         performs semiformal refinement of equivalence classes\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-R num : the max number of rounds to simulate [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-F num : the max number of frames to unroll [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-S num : the max number of rounds w/o refinement to stop [default = %d]\n", pPars->nNonRefines );
    Abc_Print( -2, "\t-M num : the min number of outputs of bounded SRM [default = %d]\n", pPars->nMinOutputs );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using two POs instead of XOR [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Choice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParChc_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManChcSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ccvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Choice(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Cec_ManChoiceComputation( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &choice [-C num] [-cvh]\n" );
    Abc_Print( -2, "\t         performs computation of structural choices\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Fraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Bnd_Man_t * pBnd;
    extern void Cec4_ManSetParams( Cec_ParFra_t * pPars );
    extern Gia_Man_t * Cec2_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars );
    extern Gia_Man_t * Cec3_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars );
    extern Gia_Man_t * Cec4_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars );
    extern void        Cec4_ManSimulateTest5( Gia_Man_t * p, int nConfs, int fVerbose );
    extern Gia_Man_t * Cec5_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars, int fCbs, int approxLim, int subBatchSz, int adaRecycle );
    extern Gia_Man_t * CecZ_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars, int nEffort );
    extern Gia_Man_t * CecU_ManPerform( Gia_Man_t * p, Cec_ParFra_t * pPars, int nOdc );
    extern Gia_Man_t * Gia_ManIvyFraig( Gia_Man_t * p, int nConfLimit, int fUseProve, int fVerbose );
    Cec_ParFra_t ParsFra, * pPars = &ParsFra; Gia_Man_t * pTemp;
    int c, fUseAlgo = 0, fUseAlgoG = 0, fUseAlgoX = 0, fUseAlgoY = 0, fUseAlgoZ = 0, fUseAlgoU = 0, fUseSave = 0, fUseIvy = 0, fUseProve = 0;
    int fCbs = 1, approxLim = 600, subBatchSz = 1, adaRecycle = 500, nMaxNodes = 0, nEffort = 25000;
    int nOdc = 3, fWordsSet = 0;
    Cec4_ManSetParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "JWRILDCNPMEOFrmdckngxyzusopwqvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->jType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->jType < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            fWordsSet = 1;
            globalUtilOptind++;
            if ( pPars->nWords < 0 )
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nItersMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nItersMax < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLevelMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 )
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
            pPars->nCallsRecycle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCallsRecycle < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGenIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGenIters < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxNodes < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nEffort = atoi(argv[globalUtilOptind++]);
            if ( nEffort < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->pDumpName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            nOdc = atoi(argv[globalUtilOptind++]);
            if ( nOdc < 0 || nOdc > 32 )
                goto usage;
            break;
        case 'r':
            pPars->fRewriting ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
            break;
        case 'c':
            pPars->fRunCSat ^= 1;
            break;
        case 'k':
            pPars->fUseCones ^= 1;
            break;
        case 'n':
            fUseAlgo ^= 1;
            break;
        case 'g':
            fUseAlgoG ^= 1;
            break;
        case 'x':
            fUseAlgoX ^= 1;
            break;
        case 'y':
            fUseAlgoY ^= 1;
            break;
        case 'z':
            fUseAlgoZ ^= 1;
            break;
        case 'u':
            fUseAlgoU ^= 1;
            break;
        case 's':
            fUseSave ^= 1;
            break;
        case 'o':
            fUseIvy ^= 1;
            break;
        case 'p':
            fUseProve ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'q':
            pPars->fBMiterInfo ^= 1;
            break;      
        case 'v':
            pPars->fVerbose ^= 1;
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
    if ( pPars->fBMiterInfo && pBnd == NULL )
    {
        Abc_Print( -1, "&fraig -q requires an initialized boundary miter.\n" );
        return 1;
    }
    if ( fUseAlgoU && (fUseAlgo || fUseAlgoG || fUseAlgoX || fUseAlgoY || fUseAlgoZ || fUseSave || fUseIvy || fUseProve) )
    {
        Abc_Print( -1, "&fraig -u cannot be combined with another sweeping mode.\n" );
        return 1;
    }
    if ( fUseSave )
    {
        Cec4_ManSimulateTest5( pAbc->pGia, pPars->nBTLimit, pPars->fVerbose );
        return 0;
    }
    else if ( fUseIvy && (!nMaxNodes || Gia_ManAndNum(pAbc->pGia) < nMaxNodes) )
        pTemp = Gia_ManIvyFraig( pAbc->pGia, pPars->nBTLimit, fUseProve, pPars->fVerbose );
    else if ( fUseAlgo )
        pTemp = Cec2_ManSimulateTest( pAbc->pGia, pPars );
    else if ( fUseAlgoG )
        pTemp = Cec3_ManSimulateTest( pAbc->pGia, pPars );
    else if ( fUseAlgoX )
        pTemp = Cec4_ManSimulateTest( pAbc->pGia, pPars );
    else if ( fUseAlgoY )
        pTemp = Cec5_ManSimulateTest( pAbc->pGia, pPars, fCbs, approxLim, subBatchSz, adaRecycle );
    else if ( fUseAlgoZ )
        pTemp = CecZ_ManSimulateTest( pAbc->pGia, pPars, nEffort );
    else if ( fUseAlgoU )
    {
        if ( !fWordsSet ) pPars->nWords = 2;
        pTemp = CecU_ManPerform( pAbc->pGia, pPars, nOdc );
    }
    else 
        pTemp = Cec_ManSatSweeping( pAbc->pGia, pPars, 0 );
    if ( pTemp == NULL )
        return 1;
    if ( pAbc->pGia->pCexSeq != NULL )
    {
        pAbc->Status  = 0;
        pAbc->nFrames = 0;
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &fraig [-JWRILDCNPMEO <num>] [-F filename] [-rmdckngxyzusopwqvh]\n" );
    Abc_Print( -2, "\t         performs combinational SAT sweeping\n" );
    Abc_Print( -2, "\t-J num : the solver type [default = %d]\n", pPars->jType );
    Abc_Print( -2, "\t-W num : the number of simulation words [default = %d; -u uses 2]\n", pPars->nWords );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-I num : the sweeping stop heuristic (-z); iteration limit otherwise [default = %d]\n", pPars->nItersMax );
    Abc_Print( -2, "\t-L num : the max number of levels of nodes to consider [default = %d]\n", pPars->nLevelMax );
    Abc_Print( -2, "\t-D num : the max speculative reduction steps (unused with -z) [default = %d]\n", pPars->nDepthMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-N num : the min number of calls to recycle the solver [default = %d]\n", pPars->nCallsRecycle );
    Abc_Print( -2, "\t-P num : the number of pattern generation iterations [default = %d]\n", pPars->nGenIters );
    Abc_Print( -2, "\t-M num : the node count limit to call the old sweeper [default = %d]\n", nMaxNodes );
    Abc_Print( -2, "\t-E num : -z max conflicts = min(C, E * gain^2) (0 = use -C) [default = %d]\n", nEffort );
    Abc_Print( -2, "\t         constants, miter mode, and CO drivers retain the full -C budget\n" );
    Abc_Print( -2, "\t-O num : -u max fanout levels for observability don't-cares (0..32) [default = %d]\n", nOdc );
    Abc_Print( -2, "\t-F file: the file name to dump primary output information [default = none]\n" );
    Abc_Print( -2, "\t-r     : toggle the use of AIG rewriting [default = %s]\n", pPars->fRewriting? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using double output miters [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based solver [default = %s]\n", pPars->fRunCSat? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle using logic cones in the SAT solver [default = %s]\n", pPars->fUseCones? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle using new implementation [default = %s]\n", fUseAlgo? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using another new implementation [default = %s]\n", fUseAlgoG? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle using another new implementation [default = %s]\n", fUseAlgoX? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle using another new implementation [default = %s]\n", fUseAlgoY? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle sweeping with cached local proofs [default = %s]\n", fUseAlgoZ? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle one-pass ODC constant removal (-C shared across care cubes) [default = %s]\n", fUseAlgoU? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle dumping equivalences into a file [default = %s]\n", fUseSave? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using the old SAT sweeper [default = %s]\n", fUseIvy? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle trying to prove when running the old SAT sweeper [default = %s]\n", fUseProve? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing even more verbose information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle recording mappings for an initialized boundary miter [default = %s]\n", pPars->fBMiterInfo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9CFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    Ssc_Pars_t Pars, * pPars = &Pars;
    Ssc_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCacvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'a':
            pPars->fAppend ^= 1;
            break;
        case 'c':
            pPars->fVerify ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9CFraig(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Ssc_PerformSweepingConstr( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &cfraig [-WC <num>] [-acvh]\n" );
    Abc_Print( -2, "\t         performs combinational SAT sweeping under constraints\n" );
    Abc_Print( -2, "\t         which are present in the AIG or set manually using \"constr\"\n" );
    Abc_Print( -2, "\t         (constraints are listed as last POs and true when they are 0)\n" );
    Abc_Print( -2, "\t-W num : the number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-a     : toggle appending constraints to the result [default = %s]\n", pPars->fAppend? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle performing internal verification [default = %s]\n", pPars->fVerify? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Srm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileNameIn = NULL;
    char pFileName[10] = "gsrm.aig", pFileName2[10] = "gsyn.aig";
    Gia_Man_t * pTemp, * pAux;
    int c, fVerbose = 0;
    int fSynthesis = 0;
    int fSpeculate = 1;
    int fSkipSome = 0;
    int fDualOut = 0;
    int fComb = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Adrsfcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileNameIn = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'd':
            fDualOut ^= 1;
            break;
        case 'r':
            fSynthesis ^= 1;
            break;
        case 's':
            fSpeculate ^= 1;
            break;
        case 'f':
            fSkipSome ^= 1;
            break;
        case 'c':
            fComb ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Srm(): There is no AIG.\n" );
        return 1;
    }
    if ( fComb )
    {
        extern int Cec4_ManSimulateOnlyTest( Gia_Man_t * p, int fVerbose );
        int Result = Cec4_ManSimulateOnlyTest( pAbc->pGia, fVerbose );
        extern Gia_Man_t * Gia_ManCombSpecReduce( Gia_Man_t * p );
        pTemp = Gia_ManCombSpecReduce( pAbc->pGia );
        Abc_FrameUpdateGia( pAbc, pTemp );
        Result = 0;
        return 0;
    }
    sprintf(pFileName,  "gsrm%s.aig", fSpeculate? "" : "s" );
    sprintf(pFileName2, "gsyn%s.aig", fSpeculate? "" : "s" );
    pTemp = Gia_ManSpecReduce( pAbc->pGia, fDualOut, fSynthesis, fSpeculate, fSkipSome, fVerbose );
    if ( pTemp )
    {
        if ( fSpeculate )
        {
            pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
            Gia_ManStop( pAux );
        }
        Gia_AigerWrite( pTemp, pFileNameIn ? pFileNameIn : pFileName, 0, 0, 0 );
        Abc_Print( 1, "Speculatively reduced model was written into file \"%s\".\n", pFileName );
        Gia_ManPrintStatsShort( pTemp );
        Gia_ManStop( pTemp );
    }
    if ( fSynthesis )
    {
        pTemp = Gia_ManEquivReduce( pAbc->pGia, 1, fDualOut, 0, fVerbose );
        if ( pTemp )
        {
            pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
            Gia_ManStop( pAux );

            Gia_AigerWrite( pTemp, pFileName2, 0, 0, 0 );
            Abc_Print( 1, "Reduced original network was written into file \"%s\".\n", pFileName2 );
            Gia_ManPrintStatsShort( pTemp );
            Gia_ManStop( pTemp );
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &srm [-A file] [-drsfcvh]\n" );
    Abc_Print( -2, "\t          derives or writes speculatively reduced model into file \"%s\"\n", pFileName );
    Abc_Print( -2, "\t-A file : file name for dumping speculative-reduced model [default = \"gsrm.aig\"]\n" );
    Abc_Print( -2, "\t-d      : toggle creating dual-output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-r      : toggle writing reduced network for synthesis [default = %s]\n", fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-s      : toggle using speculation at the internal nodes [default = %s]\n", fSpeculate? "yes": "no" );
    Abc_Print( -2, "\t-f      : toggle filtering to remove redundant equivalences [default = %s]\n", fSkipSome? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggle using combinational speculation [default = %s]\n", fComb? "yes": "no" );
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
int Abc_CommandAbc9Srm2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char pFileName[10], * pFileName1, * pFileName2;
    Gia_Man_t * pTemp, * pAux;
    int fLatchA = 0, fLatchB = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "abvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fLatchA ^= 1;
            break;
        case 'b':
            fLatchB ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->pReprs == NULL || pAbc->pGia->pNexts == NULL )
    {
        Abc_Print( -1, "Equivalences are not defined.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): Expecting two file names on the command line.\n" );
        return 1;
    }
    // get the input file name
    pFileName1 = argv[globalUtilOptind];
    pFileName2 = argv[globalUtilOptind+1];
    // create file name
    sprintf(pFileName,  "gsrm.aig" );
    pTemp = Gia_ManDup( pAbc->pGia );
    // copy equivalences
    pTemp->pReprs = ABC_ALLOC( Gia_Rpr_t, Gia_ManObjNum(pTemp) );
    memcpy( pTemp->pReprs, pAbc->pGia->pReprs, sizeof(Gia_Rpr_t) * Gia_ManObjNum(pTemp) );
    pTemp->pNexts = ABC_ALLOC( int, Gia_ManObjNum(pTemp) );
    memcpy( pTemp->pNexts, pAbc->pGia->pNexts, sizeof(int) * Gia_ManObjNum(pTemp) );
//Gia_ManPrintStats( pTemp, 0 );
    // filter the classes
    if ( !Gia_ManFilterEquivsForSpeculation( pTemp, pFileName1, pFileName2, fLatchA, fLatchB ) )
    {
        Gia_ManStop( pTemp );
        Abc_Print( -1, "Filtering equivalences has failed.\n" );
        return 1;
    }
//Gia_ManPrintStats( pTemp, 0 );
    pTemp = Gia_ManSpecReduce( pAux = pTemp, 0, 0, 1, 0, 0 );
    Gia_ManStop( pAux );
    if ( pTemp )
    {
        pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
        Gia_ManStop( pAux );

        Gia_AigerWrite( pTemp, pFileName, 0, 0, 0 );
        Abc_Print( 1, "Speculatively reduced model was written into file \"%s\".\n", pFileName );
        Gia_ManPrintStatsShort( pTemp );
        Gia_ManStop( pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &srm2 [-abvh] <PartA_FileName> <PartB_FileName>\n" );
    Abc_Print( -2, "\t         writes speculatively reduced model into file \"%s\"\n", pFileName );
    Abc_Print( -2, "\t         only preserves equivalences across PartA and PartB\n" );
    Abc_Print( -2, "\t-a     : toggle using latches only in PartA [default = %s]\n", fLatchA? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle using latches only in PartB [default = %s]\n", fLatchB? "yes": "no" );
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
int Abc_CommandAbc9Filter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName1 = NULL, * pFileName2 = NULL;
    int fFlopsOnly = 0, fFlopsWith = 0, fUseRiDrivers = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fgivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFlopsOnly ^= 1;
            break;
        case 'g':
            fFlopsWith ^= 1;
            break;
        case 'i':
            fUseRiDrivers ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->pReprs == NULL || pAbc->pGia->pNexts == NULL )
    {
        Abc_Print( -1, "Equivalences are not defined.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind && argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): Expecting two file names on the command line.\n" );
        return 1;
    }
    // filter using one of the choices
    if ( fFlopsOnly ^ fFlopsWith )
        Gia_ManFilterEquivsUsingLatches( pAbc->pGia, fFlopsOnly, fFlopsWith, fUseRiDrivers );
    // get the input file name
    if ( argc == globalUtilOptind + 2 )
    {
        pFileName1 = argv[globalUtilOptind];
        pFileName2 = argv[globalUtilOptind+1];
        if ( !Gia_ManFilterEquivsUsingParts( pAbc->pGia, pFileName1, pFileName2 ) )
        {
            Abc_Print( -1, "Filtering equivalences using PartA and PartB has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &filter [-fgivh] <PartA_FileName> <PartB_FileName>\n" );
    Abc_Print( -2, "\t         performs filtering of equivalence classes\n" );
    Abc_Print( -2, "\t         (if Parts A/B are given, removes classes composed of one part)\n" );
    Abc_Print( -2, "\t-f     : toggle removing all elements except flops [default = %s]\n", fFlopsOnly? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle removing classes without flops [default = %s]\n", fFlopsWith? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle using flop inputs instead of flop outputs [default = %s]\n", fUseRiDrivers? "yes": "no" );
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
int Abc_CommandAbc9Reduce( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp, * pTemp2;
    int c, fVerbose = 0;
    int fUseAll = 0;
    int fDualOut = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "advh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fUseAll ^= 1;
            break;
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
        Abc_Print( -1, "Abc_CommandAbc9Reduce(): There is no AIG.\n" );
        return 1;
    }
    if ( fUseAll )
    {
        pTemp = Gia_ManEquivReduce( pAbc->pGia, fUseAll, fDualOut, 0, fVerbose );
        pTemp = Gia_ManSeqStructSweep( pTemp2 = pTemp, 1, 1, 0 );
        Gia_ManStop( pTemp2 );
    }
    else
        pTemp = Gia_ManEquivReduceAndRemap( pAbc->pGia, 1, fDualOut );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &reduce [-advh]\n" );
    Abc_Print( -2, "\t         reduces the circuit using equivalence classes\n" );
    Abc_Print( -2, "\t-a     : toggle merging all equivalences [default = %s]\n", fUseAll? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle using dual-output merging [default = %s]\n", fDualOut? "yes": "no" );
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
int Abc_CommandAbc9EquivMark( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManEquivMark( Gia_Man_t * p, char * pFileName, int fSkipSome, int fVerbose );
    char * pFileName;
    int c, fVerbose = 0;
    int fSkipSome = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fSkipSome ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9EquivMark(): There is no AIG.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    // get the input file name
    pFileName = argv[globalUtilOptind];
    // mark equivalences
    Gia_ManEquivMark( pAbc->pGia, pFileName, fSkipSome, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv_mark [-fvh] <miter.aig>\n" );
    Abc_Print( -2, "\t              marks equivalences using an external miter\n" );
    Abc_Print( -2, "\t-f          : toggle the use of filtered equivalences [default = %s]\n", fSkipSome? "yes": "no" );
    Abc_Print( -2, "\t-v          : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h          : print the command usage\n");
    Abc_Print( -2, "\t<miter.aig> : file with the external miter to read\n");
    Abc_Print( -2, "\t              \n" );
    Abc_Print( -2, "\t              The external miter should be generated by &srm -s\n" );
    Abc_Print( -2, "\t              and (partially) solved by any verification engine(s).\n" );
    Abc_Print( -2, "\t              The external miter should have as many POs as\n" );
    Abc_Print( -2, "\t              the number of POs in the current AIG plus\n" );
    Abc_Print( -2, "\t              the number of equivalences in the current AIG.\n" );
    Abc_Print( -2, "\t              If some POs are proved, the corresponding equivs\n" );
    Abc_Print( -2, "\t              are marked as proved, to be reduced by &reduce.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9EquivFilter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManEquivFilter( Gia_Man_t * p, Vec_Int_t * vPoIds, int fVerbose );
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
        Abc_Print( -1, "Abc_CommandAbc9EquivFilter(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManEquivFilter( pAbc->pGia, pAbc->vAbcObjIds, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv_filter [-vh]\n" );
    Abc_Print( -2, "\t              filters equivalence candidates after disproving some SRM outputs\n" );
    Abc_Print( -2, "\t              (the array of disproved outputs should be given as pAbc->vAbcObjIds)\n" );
    Abc_Print( -2, "\t-v          : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h          : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    Dch_Pars_t Pars, * pPars = &Pars;
    int c;
    Dch_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCStvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 )
                goto usage;
            break;
        case 't':
            pPars->fSimulateTfo ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Sweep(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) && pAbc->pGia->pAigExtra == NULL )
    {
        printf( "Timing manager is given but there is no GIA of boxes.\n" );
        return 0;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) )
        pTemp = Gia_ManSweepWithBoxes( pAbc->pGia, pPars, NULL, 0, 0, pPars->fVerbose, 0 );
    else
        pTemp = Gia_ManFraigSweepSimple( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &sweep [-WCS num] [-tvh]\n" );
    Abc_Print( -2, "\t         performs SAT sweeping for AIG with boxes\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-t     : toggle simulation of the TFO classes [default = %s]\n", pPars->fSimulateTfo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Speedup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int c, fVeryVerbose;

    // set defaults
    fUseLutLib   = 0;
    Percentage   = 5;
    Degree       = 2;
    fVerbose     = 0;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): There is no AIG to map.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pAbc->pGia->pLutLib = fUseLutLib ? pAbc->pLibLut : NULL;
    pTemp = Gia_ManSpeedup( pAbc->pGia, Percentage, Degree, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &speedup [-P num] [-N num] [-lvwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to speedup the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : delay delta defining critical path for library model [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
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
int Abc_CommandAbc9Dch2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDch2( Gia_Man_t * p, int nSnapshots, int nConfs, int nConfsChoice, int fKeepLevel, int fVerbose );
    Gia_Man_t * pNew;
    int c, nSnapshots = 2, nConfs = 100, nConfsChoice = 30, fKeepLevel = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NCSlvh")) != EOF )
    {
        switch ( c )
        {
        case 'N':
        case 'C':
        case 'S':
        {
            char * pEnd;
            const char * pArg;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            pArg = argv[globalUtilOptind++];
            errno = 0;
            Value = strtol( pArg, &pEnd, 10 );
            if ( errno || pEnd == pArg || *pEnd || Value < 0 || Value > INT_MAX ) goto usage;
            if ( c == 'N' ) nSnapshots = (int)Value;
            else if ( c == 'C' ) nConfs = (int)Value;
            else nConfsChoice = (int)Value;
            break;
        }
        case 'l': fKeepLevel ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc || (nSnapshots != 2 && nSnapshots != 3) ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&dch2: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManHasChoices(pAbc->pGia) || Gia_ManMuxNum(pAbc->pGia) ||
         Gia_ManXorNum(pAbc->pGia) || Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&dch2: This command requires an AIG without choices, XOR/MUX nodes, or barrier buffers.\n" );
        return 1;
    }
    pNew = Gia_ManDch2( pAbc->pGia, nSnapshots, nConfs, nConfsChoice, fKeepLevel, fVerbose );
    if ( !pNew )
    {
        Abc_Print( -1, "&dch2: Choice computation has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &dch2 [-NCS num] [-lvh]\n" );
    Abc_Print( -2, "\t         computes structural choices from fast synthesis snapshots\n" );
    Abc_Print( -2, "\t         two snapshots use optimized AIGs; three also include the input\n" );
    Abc_Print( -2, "\t         conflict limits apply to each SAT call; 0 means unlimited\n" );
    Abc_Print( -2, "\t-N num : number of snapshots, 2 or 3 [default = %d]\n", nSnapshots );
    Abc_Print( -2, "\t-C num : primary (same-snapshot) conflict limit [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-S num : secondary (cross-snapshot) conflict limit [default = %d]\n", nConfsChoice );
    Abc_Print( -2, "\t-l     : toggle preserving synthesis logic levels [default = %s]\n", fKeepLevel ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes structural choices with the established synthesis flow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManEquivReduce2( Gia_Man_t * p, int fRandom );
    Gia_Man_t * pTemp;
    Dch_Pars_t Pars, * pPars = &Pars;
    int c, fMinLevel = 0, fEquiv = 0, fRandom = 0;
    // set defaults
    Dch_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCSsptfremngcxyvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 )
                goto usage;
            break;
        case 's':
            pPars->fSynthesis ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 't':
            pPars->fSimulateTfo ^= 1;
            break;
        case 'f':
            pPars->fLightSynth ^= 1;
            break;
        case 'r':
            pPars->fSkipRedSupp ^= 1;
            break;
        case 'e':
            fEquiv ^= 1;
            break;
        case 'm':
            fMinLevel ^= 1;
            break;
        case 'n':
            fRandom ^= 1;
            break;
        case 'g':
            pPars->fUseGia ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'x':
            pPars->fUseNew ^= 1;
            break;
        case 'y':
            pPars->fUseNew2 ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Dch(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Dch(): This command does not work with barrier buffers.\n" );
        return 1;
    }
    if ( fEquiv )
    {
        Aig_Man_t * pNew = Gia_ManToAigSimple( pAbc->pGia );
        assert( Gia_ManObjNum(pAbc->pGia) == Aig_ManObjNum(pNew) );
        Dch_ComputeEquivalences( pNew, (Dch_Pars_t *)pPars );
        Gia_ManReprFromAigRepr( pNew, pAbc->pGia );
        Aig_ManStop( pNew );
        pTemp = Gia_ManEquivReduce( pAbc->pGia, 1, 0, 0, 0 );
    }
    else
    {
        pTemp = Gia_ManPerformDch( pAbc->pGia, pPars );
        Abc_FrameUpdateGia( pAbc, pTemp );
        if ( fMinLevel || fRandom ) 
            pTemp = Gia_ManEquivReduce2( pAbc->pGia, fRandom );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dch [-WCS num] [-sptfremngcxyvh]\n" );
    Abc_Print( -2, "\t         computes structural choices using a new approach\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-s     : toggle synthesizing three snapshots [default = %s]\n", pPars->fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle simulation of the TFO classes [default = %s]\n", pPars->fSimulateTfo? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle using lighter logic synthesis [default = %s]\n", pPars->fLightSynth? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle skipping choices with redundant support [default = %s]\n", pPars->fSkipRedSupp? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle computing and merging equivalences [default = %s]\n", fEquiv? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle minimizing logic level after merging equivalences [default = %s]\n", fMinLevel? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle selecting random choices while merging equivalences [default = %s]\n", fRandom? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using GIA to prove equivalences [default = %s]\n", pPars->fUseGia? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT vs. MiniSat [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle using new choice computation [default = %s]\n", pPars->fUseNew? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle using new choice computation [default = %s]\n", pPars->fUseNew2? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Rpm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupReplaceCut( Gia_Man_t * p );
    Gia_Man_t * pTemp;
    int c, nCutMax   = 16;
    int fUseNaive    =  0;
    int fUseOldAlgo  =  0;
    int fVerbose     =  0;
    int fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cnavwh" ) ) != EOF )
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
        case 'n':
            fUseNaive ^= 1;
            break;
        case 'a':
            fUseOldAlgo ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Rpm(): There is no AIG.\n" );
        return 0;
    }
    if ( fUseNaive )
        pTemp = Gia_ManDupReplaceCut( pAbc->pGia );
    else if ( fUseOldAlgo )
        pTemp = Abs_RpmPerformOld( pAbc->pGia, fVerbose );
    else
        pTemp = Abs_RpmPerform( pAbc->pGia, nCutMax, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &rpm [-C num] [-navwh]\n" );
    Abc_Print( -2, "\t         performs structural reparametrization\n" );
    Abc_Print( -2, "\t-C num : max cut size for testing range equivalence [default = %d]\n", nCutMax );
    Abc_Print( -2, "\t-n     : toggle using naive reparametrization [default = %s]\n", fUseNaive? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using old algorithm [default = %s]\n", fUseOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing more verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
