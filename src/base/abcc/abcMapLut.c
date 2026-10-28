/**CFile****************************************************************

  FileName    [abcMapLut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [LUT mapping and timing.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "map/fpga/fpga.h"
#include "opt/lpk/lpk.h"
#include "map/mpm/mpm.h"
#include "bool/kit/kit.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandLutAbsorb                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutpack                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutmin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTrace                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCascade                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutCasDec              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutCas                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBsEval                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoiceLut         ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandFpga                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandFpgaFast               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIf                     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIfif                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqFpga                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9False              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Flow               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Flow2              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Flow3              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9If                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Iff                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Iiff               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9If2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9If3                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9If2Old             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sif                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Jf                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Kf                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Lf                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Mf                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Of                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Pack               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Edge               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatLut             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LNetMap            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Unmap              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Trace              ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers lut mapping and timing commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitMapLut( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutabsorb",     Abc_CommandLutAbsorb,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutpack",       Abc_CommandLutpack,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutmin",        Abc_CommandLutmin,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "trace",         Abc_CommandTrace,            0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cascade",       Abc_CommandCascade,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutcasdec",     Abc_CommandLutCasDec,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutcas",        Abc_CommandLutCas,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "bseval",        Abc_CommandBsEval,           0 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "supercl",       Abc_CommandSuperChoiceLut,   1 );
//    Cmd_CommandAdd( pAbc, "FPGA mapping", "fpga",          Abc_CommandFpga,             1 );
//    Cmd_CommandAdd( pAbc, "FPGA mapping", "ffpga",         Abc_CommandFpgaFast,         1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "if",            Abc_CommandIf,               1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "ifif",          Abc_CommandIfif,             1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "sfpga",         Abc_CommandSeqFpga,          1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&false",        Abc_CommandAbc9False,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&flow",         Abc_CommandAbc9Flow,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&flow2",        Abc_CommandAbc9Flow2,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&flow3",        Abc_CommandAbc9Flow3,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&if",           Abc_CommandAbc9If,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&iff",          Abc_CommandAbc9Iff,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&iiff",         Abc_CommandAbc9Iiff,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&if2",          Abc_CommandAbc9If2,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&if3",          Abc_CommandAbc9If3,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&if2old",       Abc_CommandAbc9If2Old,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sif",          Abc_CommandAbc9Sif,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&jf",           Abc_CommandAbc9Jf,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&kf",           Abc_CommandAbc9Kf,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lf",           Abc_CommandAbc9Lf,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mf",           Abc_CommandAbc9Mf,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&of",           Abc_CommandAbc9Of,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&pack",         Abc_CommandAbc9Pack,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&edge",         Abc_CommandAbc9Edge,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&satlut",       Abc_CommandAbc9SatLut,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lnetmap",      Abc_CommandAbc9LNetMap,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&unmap",        Abc_CommandAbc9Unmap,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&trace",        Abc_CommandAbc9Trace,        0 );
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
int Abc_CommandLutAbsorb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    If_LibLut_t * pLutLib = (If_LibLut_t *)Abc_FrameReadLibLut();
    int c, nInit, nRemoved, fKgiven = 0;
    int nLutSize   = pLutLib? Abc_MinInt(6, pLutLib->LutMax) : 6;
    int nFanoutMax = 8;
    int nRounds    = 1;
    int fVerbose   = 0;
    float AreaGain = 0.0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            fKgiven = 1;
            if ( nLutSize < 2 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nFanoutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFanoutMax < 2 )
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
            if ( nRounds < 1 )
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
        Abc_Print( -1, "The network should be a LUT-mapped logic network.\n" );
        return 1;
    }
    if ( pLutLib && pLutLib->LutMax < 2 )
    {
        Abc_Print( -1, "The LUT library max LUT size (%d) is less than 2.\n", pLutLib->LutMax );
        return 1;
    }
    if ( pLutLib && nLutSize > pLutLib->LutMax )
    {
        if ( fKgiven )
            Abc_Print( 1, "lutabsorb: -K %d exceeds the LUT library max %d; using %d.\n",
                nLutSize, pLutLib->LutMax, pLutLib->LutMax );
        nLutSize = pLutLib->LutMax;
    }
    if ( !Abc_NtkHasAig(pNtk) && !Abc_NtkToAig(pNtk) )
    {
        Abc_Print( -1, "Converting node functions to AIGs has failed.\n" );
        return 1;
    }
    if ( pLutLib && Abc_NtkGetFaninMax(pNtk) > pLutLib->LutMax )
        Abc_Print( ABC_WARNING, "The network has nodes with up to %d fanins, but the LUT library max is %d; candidates involving larger nodes are skipped.\n",
            Abc_NtkGetFaninMax(pNtk), pLutLib->LutMax );
    nInit = Abc_NtkNodeNum(pNtk);
    nRemoved = Abc_NtkLutAbsorb( pNtk, nLutSize, nFanoutMax, nRounds, fVerbose, pLutLib, &AreaGain );
    Abc_Print( 1, "lutabsorb: K=%d M=%d R=%d  nodes %d -> %d (-%d)  area gain %.2f\n",
        nLutSize, nFanoutMax, nRounds, nInit, Abc_NtkNodeNum(pNtk), nRemoved, AreaGain );
    return 0;

usage:
    Abc_Print( -2, "usage: lutabsorb [-KMR num] [-vh]\n" );
    Abc_Print( -2, "\t         absorbs multi-fanout LUTs into all their fanout LUTs when every result fits in K inputs\n" );
    Abc_Print( -2, "\t-K num : the max LUT size after absorption [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t         values above the current LUT library max are truncated to it\n" );
    Abc_Print( -2, "\t-M num : the max fanout count of a candidate node [default = %d]\n", nFanoutMax );
    Abc_Print( -2, "\t-R num : the number of passes [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutpack( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Lpk_Par_t Pars, * pPars = &Pars;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    memset( pPars, 0, sizeof(Lpk_Par_t) );
    pPars->nLutsMax     =  4; // (N) the maximum number of LUTs in the structure
    pPars->nLutsOver    =  3; // (Q) the maximum number of LUTs not in the MFFC
    pPars->nVarsShared  =  0; // (S) the maximum number of shared variables (crossbars)
    pPars->nGrowthLevel =  0; // (L) the maximum number of increased levels
    pPars->fSatur       =  1;
    pPars->fZeroCost    =  0;
    pPars->fFirst       =  0;
    pPars->fOldAlgo     =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NQSLszfovwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutsMax < 2 || pPars->nLutsMax > 16 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutsOver = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutsOver < 0 || pPars->nLutsOver > 8 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVarsShared = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVarsShared < 0 || pPars->nVarsShared > 4 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY )
                goto usage;
            break;
        case 's':
            pPars->fSatur ^= 1;
            break;
        case 'z':
            pPars->fZeroCost ^= 1;
            break;
        case 'f':
            pPars->fFirst ^= 1;
            break;
        case 'o':
            pPars->fOldAlgo ^= 1;
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
    if ( pPars->nVarsShared < 0 || pPars->nVarsShared > 3 )
    {
        Abc_Print( -1, "The number of shared variables (%d) is not in the range 0 <= S <= 3.\n", pPars->nVarsShared );
        return 1;
    }

    // modify the current network
    if ( !Lpk_Resynthesize( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: lutpack [-NQSL <num>] [-szfovwh]\n" );
    Abc_Print( -2, "\t           performs \"rewriting\" for LUT network;\n" );
    Abc_Print( -2, "\t           determines LUT size as the max fanin count of a node;\n" );
    Abc_Print( -2, "\t           if the network is not LUT-mapped, packs it into 6-LUTs\n" );
    Abc_Print( -2, "\t           (there is another command for resynthesis after LUT mapping, \"mfs2\")\n" );
    Abc_Print( -2, "\t-N <num> : the max number of LUTs in the structure (2 <= num) [default = %d]\n", pPars->nLutsMax );
    Abc_Print( -2, "\t-Q <num> : the max number of LUTs not in MFFC (0 <= num) [default = %d]\n", pPars->nLutsOver );
    Abc_Print( -2, "\t-S <num> : the max number of LUT inputs shared (0 <= num <= 3) [default = %d]\n", pPars->nVarsShared );
    Abc_Print( -2, "\t-L <num> : max level increase after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-s       : toggle iteration till saturation [default = %s]\n", pPars->fSatur? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle zero-cost replacements [default = %s]\n", pPars->fZeroCost? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggle using only first node and first cut [default = %s]\n", pPars->fFirst? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggle using old implementation [default = %s]\n", pPars->fOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle detailed printout of decomposed functions [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutmin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkLutmin( Abc_Ntk_t * pNtk, int nLutSize, int fReorder, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c;
    int nLutSize = 4;
    int fReorder = 1;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Krvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'r':
            fReorder ^= 1;
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
    // modify the current network
    pNtkRes = Abc_NtkLutmin( pNtk, nLutSize, fReorder, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lutmin [-K <num>] [-rvh]\n" );
    Abc_Print( -2, "\t           perform FPGA mapping while minimizing the LUT count\n" );
    Abc_Print( -2, "\t           as described in the paper T. Sasao and A. Mishchenko:\n" );
    Abc_Print( -2, "\t           \"On the number of LUTs to implement logic functions\".\n" );
    Abc_Print( -2, "\t-K <num> : the LUT size to use for the mapping (2 <= num) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-r       : toggle using BDD variable reordering [default = %s]\n", fReorder? "yes": "no" );
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
int Abc_CommandTrace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLutLib;
    int fVerbose;
    extern void Abc_NtkDelayTracePrint( Abc_Ntk_t * pNtk, int fUseLutLib, int fVerbose );

    // set defaults
    fUseLutLib = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLutLib ^= 1;
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
    Abc_NtkDelayTracePrint( pNtk, fUseLutLib, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: trace [-lvh]\n" );
    Abc_Print( -2, "\t           performs delay trace of LUT-mapped network\n" );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib": "unit" );
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
int Abc_CommandCascade( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLutSize;
    int fCheck;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nLutSize = 12;
    fCheck   = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kcvh" ) ) != EOF )
    {
        switch ( c )
        {
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty neAtwork.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCascade( pNtk, nLutSize, fCheck, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes = Abc_NtkCascade( pNtk, nLutSize, fCheck, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Cascade synthesis has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cascade [-K <num>] [-cvh]\n" );
    Abc_Print( -2, "\t           performs LUT cascade synthesis for the current network\n" );
    Abc_Print( -2, "\t-K <num> : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-c       : check equivalence after synthesis [default = %s]\n", fCheck? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t           \n");
    Abc_Print( -2, "  A lookup-table cascade is a programmable architecture developed by\n");
    Abc_Print( -2, "  Professor Tsutomu Sasao (sasao@cse.kyutech.ac.jp) at Kyushu Institute\n");
    Abc_Print( -2, "  of Technology. This work received Takeda Techno-Entrepreneurship Award:\n");
    Abc_Print( -2, "  http://www.lsi-cad.com/sasao/photo/takeda.html\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutCasDec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkLutCascadeGen( int nLutSize, int nStages, int nRails, int nShared, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkLutCascadeOne( Abc_Ntk_t * pNtk, int nLutSize, int nLuts, int nRails, int nIters, int nJRatio, int nZParam, int fXRail, int Seed, int fVerbose, int fVeryVerbose, char * pGuide, int nSubsets, int nBest );
    extern void        Abc_NtkLutCascadeFile( char * pFileName, int nVarNum, int nLutSize, int nLuts, int nRails, int nIters, int nJRatio, int nZParam, int Seed, int fVerbose, int fVeryVerbose, int fPrintMyu, int fPrintLev, int fXRail, int nSubsets, int nBest, int fDump );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes; char * pGuide = NULL, * pFileName = NULL;
    int c, nVarNum = -1, nLutSize = 6, nStages = 8, nRails = 1, nShared = 2, Seed = 0, nIters = 10, nJRatio = -1, nZParam = 5, fGen = 0, fPrintMyu = 0, fPrintLev = 0, fXRail = 0, nSubsets = 0, nBest = 0, fDump = 0, fVerbose = 0, fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMRSCIZNGBFgmlxdvwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nStages = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStages < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRails = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRails < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nShared = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nShared < 0 )
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
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            nJRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nJRatio < 0 )
                goto usage;
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by a file name.\n" );
                goto usage;
            }
            nZParam = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
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
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nSubsets = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSubsets < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBest = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBest < 0 )
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
        case 'g':
            fGen ^= 1;
            break;
        case 'm':
            fPrintMyu ^= 1;
            break;
        case 'l':
            fPrintLev ^= 1;
            break;
        case 'x':
            fXRail ^= 1;
            break;
        case 'd':
            fDump ^= 1;
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
    if ( pFileName ) 
    {
        if ( nVarNum == -1 ) 
        {
            Abc_Print( -1, "The number of variables should be given on the command line using switch \"-N <num>\".\n" );
            return 1;
        }
        Abc_NtkLutCascadeFile( pFileName, nVarNum, nLutSize, nStages, nRails, nIters, nJRatio, nZParam, Seed, fVerbose, fVeryVerbose, fPrintMyu, fPrintLev, fXRail, nSubsets, nBest, fDump );
        return 0;
    }
    if ( fGen )
    {
        pNtkRes = Abc_NtkLutCascadeGen( nLutSize, nStages, nRails, nShared, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "LUT cascade generation failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkCoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "This command is currently applicable only to single-output networks.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Run command \"strash\" to convert the network into an AIG.\n" );
        return 1;
    }
    if ( Abc_NtkCiNum(pNtk) > nLutSize + (nLutSize - nRails) * (nStages - 1) )
    {
        Abc_Print( -1, "Cannot decompose %d-input function into a %d-rail cascade of %d %d-LUTs (max suppose size = %d).\n", 
            Abc_NtkCiNum(pNtk), nRails, nStages, nLutSize, nLutSize + (nLutSize - nRails) * (nStages - 1) );
        return 1;
    }
    if ( argc == globalUtilOptind + 1 )
        pGuide = argv[globalUtilOptind];
    pNtkRes = Abc_NtkLutCascadeOne( pNtk, nLutSize, nStages, nRails, nIters, nJRatio, nZParam, fXRail, Seed, fVerbose, fVeryVerbose, pGuide, nSubsets, nBest );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "LUT cascade mapping failed.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lutcasdec [-KMRCSIZNGB <num>] [-F <file>] [-gmlxdvwh]\n" );
    Abc_Print( -2, "\t           decomposes the primary output functions into LUT cascades\n" );
    Abc_Print( -2, "\t-K <num> : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-M <num> : the maximum delay (the number of stages) [default = %d]\n", nStages );
    Abc_Print( -2, "\t-R <num> : the number of direct connections (rails) [default = %d]\n", nRails );
    Abc_Print( -2, "\t-C <num> : the number of shared variables in each stage [default = %d]\n", nShared );
    Abc_Print( -2, "\t-S <num> : the random seed for randomized bound-set selection [default = %d]\n", Seed );
    Abc_Print( -2, "\t-I <num> : the number of iterations when looking for a solution [default = %d]\n", nIters );
    //Abc_Print( -2, "\t-J <num> : toggle using random bound-set every this many iterations [default = %d]\n", nJRatio );
    Abc_Print( -2, "\t-Z <num> : the number determining how many decompositions are tried  [default = %d]\n", nZParam );
    Abc_Print( -2, "\t-N <num> : the number of support variables (for truth table files only) [default = unused]\n" );
    Abc_Print( -2, "\t-G <num> : the number of variable groups to consider [default = %d]\n", nSubsets );
    Abc_Print( -2, "\t-B <num> : the number of best groups to use as bound-sets [default = %d]\n", nBest );
    Abc_Print( -2, "\t-F <file>: a text file with truth tables in hexadecimal listed one per line\n");    
    Abc_Print( -2, "\t-g       : toggle generating random cascade with these parameters [default = %s]\n", fGen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggle printing column multiplicity statistics [default = %s]\n", fPrintMyu? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggle printing level counting statistics [default = %s]\n", fPrintLev? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggle using extended cascade decomposition [default = %s]\n", fXRail? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggle dumping non-decomposable functions into a file [default = %s]\n", fDump? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle additional verbose printout [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutCas( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkLutCascadeMap( Abc_Ntk_t * pNtk, int nLutsMax, int nIters, int fDelayLut, int fDelayRoute, int fDelayDirect, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c, nLutSize = 6, nLutsMax = 8, nIters = 1000, Seed = 0, fVerbose = 0;
    int fDelayLut = 10, fDelayRoute = 30, fDelayDirect = 3;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMISLWDfvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutsMax < 0 )
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            fDelayLut = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fDelayLut < 0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            fDelayRoute = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fDelayRoute < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            fDelayDirect = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fDelayDirect < 0 )
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
        Abc_Print( -1, "Run command \"if\" or any other LUT mapper to map the current network into LUTs.\n" );
        return 1;
    }
    if ( Abc_NtkGetFaninMax(pNtk) > nLutSize )
    {
        Abc_Print( -1, "The current network contains nodes with fanin count (%d) exceeding the LUT size (%d).\n", Abc_NtkGetFaninMax(pNtk), nLutSize );
        return 1;            
    }
    srand( Seed );
    pNtkRes = Abc_NtkLutCascadeMap( pNtk, nLutsMax, nIters, fDelayLut, fDelayRoute, fDelayDirect, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "LUT cascade mapping failed.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lutcas [-KMISLWD <num>] [-vh]\n" );
    Abc_Print( -2, "\t           decomposes the current network into LUT cascades\n" );
    Abc_Print( -2, "\t-K <num> : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-M <num> : the maximum number of LUTs in the cascade [default = %d]\n", nLutsMax );
    Abc_Print( -2, "\t-I <num> : the number of iterations when looking for a solution [default = %d]\n", nIters );
    Abc_Print( -2, "\t-S <num> : the random seed used to randimize solutions [default = %d]\n", Seed );
    Abc_Print( -2, "\t-L <num> : the intrinsic LUT delay [default = %d]\n", fDelayLut );
    Abc_Print( -2, "\t-W <num> : the routable wire delay [default = %d]\n", fDelayRoute );
    Abc_Print( -2, "\t-D <num> : the non-routable wire delay [default = %d]\n", fDelayDirect );
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
int Abc_CommandBsEval( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_BSEvalOneTest( word * pT, int nVars, int nBVars, int fVerbose );
    extern void Abc_BSEvalBestTest( word * pIn, int nVars, int nBVars, int fShared, int fVerbose );
    extern void Abc_BSEvalBestGen( int nVars, int nBVars, int nFuncs, int nMints, int fTryAll, int fShared, int fVerbose );
    int c, nVars = 0, nBVars = 0, nSVars = 0, nFuncs = 0, nMints = 0, fTryAll = 0, fVerbose = 0; char * pTtStr = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IBSRMavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 2 || nVars > 16 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBVars < 1 || nBVars > 16 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nSVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSVars < 0 || nSVars > 16 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nFuncs = atoi(argv[globalUtilOptind]);
            if ( nFuncs < 1 )
                goto usage;
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
        case 'a':
            fTryAll ^= 1;
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
        pTtStr = argv[globalUtilOptind];
    if ( pTtStr ) 
    {
        nVars = Abc_Base2Log((int)strlen(pTtStr)) + 2;
        if ( (1 << (nVars-2)) != (int)strlen(pTtStr) )
        {
            Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", (1 << (nVars-2)), strlen(pTtStr) );
            return 1;
        }
    }
    if ( nVars == 0 )
    {
        Abc_Print( -1, "The number of variables should be specified on the command line.\n" );
        return 1;
    }
    if ( nBVars == 0 )
    {
        Abc_Print( -1, "The bound set size should be specified on the command line.\n" );
        return 1;
    }
    if ( nFuncs ) 
        Abc_BSEvalBestGen( nVars, nBVars, nFuncs, nMints, fTryAll, nSVars == 1, fVerbose );
    else if ( pTtStr ) 
    {
        word pTruth[1024] = {0}; 
        Abc_TtReadHex( pTruth, pTtStr );
        if ( fTryAll )
            Abc_BSEvalBestTest( pTruth, nVars, nBVars, nSVars == 1, fVerbose );
        else
            Abc_BSEvalOneTest( pTruth, nVars, nBVars, fVerbose );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: bseval [-IBSRM <num>] [-avh] <hex>\n" );
    Abc_Print( -2, "\t           bound set evaluation\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-B <num> : the number of bound set variables [default = %d]\n", nBVars );
    Abc_Print( -2, "\t-S <num> : the number of shared variables [default = %d]\n", nSVars );
    Abc_Print( -2, "\t-R <num> : the number of random functions to try [default = unused]\n" );
    Abc_Print( -2, "\t-M <num> : the number of positive minterms in the random function [default = unused]\n" );
    Abc_Print( -2, "\t-a       : toggle trying all bound sets of this size [default = %s]\n", fTryAll ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<hex>    : truth table in hex notation\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSuperChoiceLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nLutSize;
    int nCutSizeMax;
    int fVerbose;
    extern int Abc_NtkSuperChoiceLut( Abc_Ntk_t * pNtk, int nLutSize, int nCutSizeMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fVerbose = 1;
    nLutSize = 4;
    nCutSizeMax = 10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNh" ) ) != EOF )
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nCutSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutSizeMax < 0 )
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

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // convert the network into the SOP network
    pNtkRes = Abc_NtkToLogic( pNtk );

    // get the new network
    if ( !Abc_NtkSuperChoiceLut( pNtkRes, nLutSize, nCutSizeMax, fVerbose ) )
    {
        Abc_NtkDelete( pNtkRes );
        Abc_Print( -1, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: supercl [-K num] [-N num] [-vh]\n" );
    Abc_Print( -2, "\t        performs superchoicing for K-LUTs\n" );
    Abc_Print( -2, "\t        (accumulate: \"r file.blif; b; scl; f -ac; wb file_sc.blif\")\n" );
    Abc_Print( -2, "\t        (FPGA map: \"r file_sc.blif; ft; read_lut lutlibK; fpga\")\n" );
    Abc_Print( -2, "\t-K num : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-N num : the max size of the cut [default = %d]\n", nCutSizeMax );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

#if 0
/**Function*************************************************************

  Synopsis    [Handles the legacy FPGA mapper.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    char LutSize[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fSwitching;
    int fLatchPaths;
    int fVerbose;
    int nLutSize;
    float DelayTarget;

    extern Abc_Ntk_t * Abc_NtkFpga( Abc_Ntk_t * pNtk, float DelayTarget, int fRecovery, int fSwitching, int fLatchPaths, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRecovery   = 1;
    fSwitching  = 0;
    fLatchPaths = 0;
    fVerbose    = 0;
    DelayTarget =-1;
    nLutSize    =-1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "aplvhDK" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fRecovery ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
            break;
        case 'l':
            fLatchPaths ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
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
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // create the new LUT library
    if ( nLutSize >= 3 && nLutSize <= 10 )
        Fpga_SetSimpleLutLib( nLutSize );
//    else
//    {
//        Abc_Print( -1, "Cannot perform FPGA mapping with LUT size %d.\n", nLutSize );
//        return 1;
//    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%.2f", DelayTarget );
    if ( nLutSize == -1 )
        sprintf(LutSize, "library" );
    else
        sprintf(LutSize, "%d", nLutSize );
    Abc_Print( -2, "usage: fpga [-D float] [-K num] [-aplvh]\n" );
    Abc_Print( -2, "\t           performs FPGA mapping of the current network\n" );
    Abc_Print( -2, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    Abc_Print( -2, "\t-p       : optimizes power by minimizing switching activity [default = %s]\n", fSwitching? "yes": "no" );
    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < 11) [default = %s]%s\n", LutSize, (nLutSize == -1 ? " (type \"print_lut\")" : "") );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}
#endif

#if 0
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpgaFast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fVerbose;
    int nLutSize;
    float DelayTarget;

    extern Abc_Ntk_t * Abc_NtkFpgaFast( Abc_Ntk_t * pNtk, int nLutSize, int fRecovery, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRecovery   = 1;
    fVerbose    = 0;
    DelayTarget =-1;
    nLutSize    = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "avhDK" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fRecovery ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
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
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 )
        sprintf(Buffer, "not used" );
    else
        sprintf(Buffer, "%.2f", DelayTarget );
    Abc_Print( -2, "usage: ffpga [-K num] [-avh]\n" );
    Abc_Print( -2, "\t           performs fast FPGA mapping of the current network\n" );
    Abc_Print( -2, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
//    Abc_Print( -2, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < 32) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}
#endif

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    char Buffer[100], LutSize[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    If_Par_t Pars, * pPars = &Pars;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);
    If_ManSetDefaultPars( pPars );
    pPars->pLutLib = (If_LibLut_t *)Abc_FrameReadLibLut();
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFAGRNTXYZUDEWSJqalepmrsdbgxyzuoiktncfvh" ) ) != EOF )
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
            if ( pPars->nLutSize < 0 )
                goto usage;
            // if the LUT size is specified, disable library
            pPars->pLutLib = NULL;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlowIters < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaIters < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a positive integer no less than 3.\n" );
                goto usage;
            }
            pPars->nGateSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGateSize < 2 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
                return 0;
            }
            pPars->nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRelaxRatio < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer no less than 3.\n" );
                goto usage;
            }
            pPars->nNonDecLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNonDecLimit < 2 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nStructType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStructType < 0 || pPars->nStructType > 2 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nAndDelay = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAndArea < 0 )
                goto usage;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nAndArea = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAndDelay < 0 )
                goto usage;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by a positive integer 3, 4, 5, or 6.\n" );
                goto usage;
            }
            pPars->nLutDecSize = atoi(argv[globalUtilOptind]);
            pPars->fUserLut2D = 1;
            globalUtilOptind++;
            if ( pPars->nLutDecSize < 3 || pPars->nLutDecSize > 6 )
                goto usage;
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by a positive integer 3, 4, 5, or 6.\n" );
                goto usage;
            }
            pPars->nLutDecSize = atoi(argv[globalUtilOptind]);
            pPars->fUserLutDec = 1;
            globalUtilOptind++;
            if ( pPars->nLutDecSize < 3 || pPars->nLutDecSize > 6 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->Epsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Epsilon < 0.0 || pPars->Epsilon > 1.0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->WireDelay = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->WireDelay < 0.0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by string.\n" );
                goto usage;
            }
            pPars->pLutStruct = argv[globalUtilOptind];
            globalUtilOptind++;
            if ( strlen(pPars->pLutStruct) != 2 && strlen(pPars->pLutStruct) != 3 )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a 2- or 3-char string (e.g. \"44\" or \"555\").\n" );
                goto usage;
            }
            break;
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by string.\n" );
                goto usage;
            }
            pPars->pLutStruct = argv[globalUtilOptind];
            pPars->fEnableStructN = 1;
            globalUtilOptind++;
            if ( strlen(pPars->pLutStruct) != 2 && strlen(pPars->pLutStruct) != 3 )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by a 2-char string (e.g. \"44\" or \"66\" \").\n" );
                goto usage;
            }
            break;
        case 'q':
            pPars->fPreprocess ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'r':
            pPars->fExpRed ^= 1;
            break;
        //case 'f':
        //    pPars->fFancy ^= 1;
        //    break;
        case 'l':
            pPars->fLatchPaths ^= 1;
            break;
        case 'e':
            pPars->fEdge ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 's':
            pPars->fDelayOptLut ^= 1;
            break;
        case 'd':
            pPars->fBidec ^= 1;
            break;
        case 'b':
            pPars->fUseBat ^= 1;
            break;
        case 'g':
            pPars->fDelayOpt ^= 1;
            break;
        case 'x':
            pPars->fDsdBalance ^= 1;
            break;
        case 'y':
            pPars->fUserRecLib ^= 1;
            break;
        case 'u':
            pPars->fUserSesLib ^= 1;
            break;
        case 'o':
            pPars->fUseBuffs ^= 1;
            break;
        //case 'j':
        //    pPars->fEnableCheck07 ^= 1;
        //    break;
        case 'i':
            pPars->fUseCofVars ^= 1;
            break;
        case 'k':
            pPars->fUseDsdTune ^= 1;
            break;
        case 't':
            pPars->fDoAverage ^= 1;
            break;
        case 'n':
            pPars->fUseDsd ^= 1;
            break;
        case 'c':
            pPars->fUseTtPerm ^= 1;
            break;
        case 'f':
            pPars->fDumpFile ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'z':
            pPars->fDeriveLuts ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( pPars->nLutSize == -1 )
    {
        if ( pPars->pLutLib == NULL )
        {
            Abc_Print( -1, "The LUT library is not given.\n" );
            return 1;
        }
        pPars->nLutSize = pPars->pLutLib->LutMax;
    }

    if ( pPars->nLutSize < 2 || pPars->nLutSize > IF_MAX_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", pPars->nLutSize );
        return 1;
    }

    if ( pPars->nCutsMax < 1 || pPars->nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    // enable truth table computation if choices are selected
    if ( (c = Abc_NtkGetChoiceNum( pNtk )) )
    {
//        if ( !Abc_FrameReadFlag("silentmode") )
//            Abc_Print( 0, "Performing LUT mapping with %d choices.\n", c );
        pPars->fExpRed = 0;
    }

    if ( pPars->fUseBat )
    {
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature only works for {4,5,6}-LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
    }

    if ( pPars->fEnableCheck07 + pPars->fUseCofVars + pPars->fUseDsdTune + (pPars->pLutStruct != NULL) > 1 )
    {
        Abc_Print( -1, "Only one additional check can be performed at the same time.\n" );
        return 1;
    }
    if ( pPars->fEnableCheck07 )
    {
        if ( pPars->nLutSize > 9 )
        {
            Abc_Print( -1, "This feature only works for up to 9-input LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheckJ;
        pPars->fCutMin = 1;
    }
    if ( pPars->fUseCofVars )
    {
        if ( !(pPars->nLutSize & 1) )
        {
            Abc_Print( -1, "This feature only works for odd-sized LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
    }
    if ( pPars->fUseDsdTune )
    {
        If_DsdMan_t * pDsdMan = (If_DsdMan_t *)Abc_FrameReadManDsd();
        if ( pDsdMan == NULL )
        {
            Abc_Print( -1, "DSD manager is not available.\n" );
            return 1;
        }
        if ( pPars->nLutSize > If_DsdManVarNum(pDsdMan) )
        {
            Abc_Print( -1, "LUT size (%d) is more than the number of variables in the DSD manager (%d).\n", pPars->nLutSize, If_DsdManVarNum(pDsdMan) );
            return 1;
        }
        if ( pPars->fDeriveLuts && If_DsdManGetCellStr(pDsdMan) == NULL )
        {
            Abc_Print( -1, "DSD manager is not matched with any particular cell.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
        pPars->fUseDsd = 1;
        If_DsdManSetNewAsUseless( pDsdMan );
    }
    if ( pPars->pLutStruct )
    {
        if ( pPars->fDsdBalance )
        {
            Abc_Print( -1, "Incompatible options (-S and -x).\n" );
            return 1;
        }
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 16 )
        {
            Abc_Print( -1, "This feature only works for [6;16]-LUTs.\n" );
            return 1;
        }
        if ( pPars->fEnableStructN )
        {
            pPars->pFuncCell = pPars->fDelayOptLut ? NULL : If_CutPerformCheckXX;
        }
        else
        {
            pPars->pFuncCell = pPars->fDelayOptLut ? NULL : If_CutPerformCheck16;
        }
        pPars->fCutMin = 1;
        pPars->nLutDecSize = pPars->pLutStruct[0] - '0';
    }
    else
    {
        pPars->fDeriveLuts = 0;
    }

    if ( pPars->fUserLutDec || pPars->fUserLut2D )
    {
        if ( pPars->nLutDecSize == 0 )
        {
            Abc_Print( -1, "LUT decomposition size (%d) must be set.\n", pPars->nLutDecSize );
            return 1;
        }
        if ( pPars->nLutDecSize >= pPars->nLutSize )
        {
            Abc_Print( -1, "LUT size (%d) must be greater than the LUT decomposition size (%d).\n", pPars->nLutSize, pPars->nLutDecSize );
            return 1;
        }
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 11 )
        {
            Abc_Print( -1, "This feature only works for [4;11]-LUTs.\n" );
            return 1;
        }
    }

    // enable truth table computation if cut minimization is selected
    if ( pPars->fCutMin )
    {
        pPars->fTruth = 1;
        pPars->fExpRed = 0;
    }
    // modify the subgraph recording
    if ( pPars->fUserRecLib || pPars->fUserSesLib )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
    }
    // modify for delay optimization
    if ( pPars->fDelayOpt || pPars->fDsdBalance || pPars->fDelayOptLut || pPars->fUserLutDec || pPars->fUserLut2D )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUseDsd     =  pPars->fDsdBalance || pPars->fDelayOptLut;
        pPars->pLutLib     =  NULL;
    }
    // modify for delay optimization
    if ( pPars->nGateSize > 0 )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
        pPars->nLutSize    =  pPars->nGateSize;
    }

    if ( pPars->fUseDsd || pPars->fUseTtPerm )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
    }

    if ( pPars->fUseDsd )
    {
        int LutSize = (pPars->pLutStruct && pPars->pLutStruct[2] == 0)? pPars->pLutStruct[0] - '0' : 0;
        If_DsdMan_t * p = (If_DsdMan_t *)Abc_FrameReadManDsd();
        if ( pPars->pLutStruct && pPars->pLutStruct[2] != 0 )
        {
            printf( "DSD only works for LUT structures XY.\n" );
            return 0;
        }
        if ( p && pPars->nLutSize > If_DsdManVarNum(p) )
        {
            printf( "DSD manager has incompatible number of variables.\n" );
            return 0;
        }
        if ( p && LutSize != If_DsdManLutSize(p) && !pPars->fDsdBalance )
        {
            printf( "DSD manager has different LUT size.\n" );
            return 0;
        }
        if ( p == NULL )
        {
            if ( LutSize > DAU_MAX_VAR || pPars->nLutSize > DAU_MAX_VAR )
            {
                printf( "Size of required DSD manager (%d) exceeds the precompiled limit (%d) (change parameter DAU_MAX_VAR).\n", LutSize, DAU_MAX_VAR );
                return 0;
            }
            Abc_FrameSetManDsd( If_DsdManAlloc(pPars->nLutSize, LutSize) );
        }
    }

    if ( pPars->fUserRecLib )
    {
        if ( !Abc_NtkRecIsRunning3() )
        {
            printf( "LMS manager is not running (use \"rec_start3\").\n" );
            return 0;
        }
        if ( Abc_NtkRecInputNum3() != pPars->nLutSize )
        {
            printf( "The number of library inputs (%d) is different from the K parameters (%d).\n", Abc_NtkRecInputNum3(), pPars->nLutSize );
            return 0;
        }
    }

    if ( pPars->fUserSesLib )
    {
        if ( !Abc_ExactIsRunning() )
        {
            printf( "BMS manager is not running (use \"bms_start\").\n" );
            return 0;
        }
        if ( Abc_ExactInputNum() < pPars->nLutSize )
        {
            printf( "The number of library inputs (%d) is smaller than the K parameters (%d).\n", Abc_ExactInputNum(), pPars->nLutSize );
            return 0;
        }
    }

    // complain if truth tables are requested but the cut size is too large
    if ( pPars->fTruth && pPars->nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Truth tables cannot be computed for LUT larger than %d inputs.\n", IF_MAX_FUNC_LUTSIZE );
        return 1;
    }

    // disable cut-expansion if edge-based heuristics are selected
//    if ( pPars->fEdge )
//        pPars->fExpRed = 0;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        if ( !Abc_FrameReadFlag("silentmode") )
            Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkIf( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 0;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkIf( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 0;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%.2f", pPars->DelayTarget );
    if ( pPars->nLutSize == -1 )
        sprintf(LutSize, "library" );
    else
        sprintf(LutSize, "%d", pPars->nLutSize );
    Abc_Print( -2, "usage: if [-KCFAGRNTXYZMU num] [-DEW float] [-SJ str] [-qarlepmsdbgxyuoiktnczfvh]\n" );
    Abc_Print( -2, "\t           performs FPGA technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < %d) [default = %s]\n", IF_MAX_LUTSIZE+1, LutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (0 < num < 2^12) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : the number of area flow recovery iterations (num >= 0) [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations (num >= 0) [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-G num   : the max AND/OR gate size for mapping (0 = unused) [default = %d]\n", pPars->nGateSize );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n", pPars->nRelaxRatio );
    Abc_Print( -2, "\t-N num   : the max size of non-decomposable nodes [default = unused]\n", pPars->nNonDecLimit );
    Abc_Print( -2, "\t-T num   : the type of LUT structures [default = any]\n" );
    Abc_Print( -2, "\t-X num   : delay of AND-gate in LUT library units [default = %d]\n", pPars->nAndDelay );
    Abc_Print( -2, "\t-Y num   : area of AND-gate in LUT library units [default = %d]\n", pPars->nAndArea );
    Abc_Print( -2, "\t-U num   : the number of LUT inputs for delay-driven LUT decomposition [default = not used]\n" );
    Abc_Print( -2, "\t-Z num   : the number of LUT inputs for delay-driven LUT decomposition [default = not used]\n" );
    Abc_Print( -2, "\t-D float : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->Epsilon );
    Abc_Print( -2, "\t-W float : sets wire delay between adjects LUTs [default = %f]\n", pPars->WireDelay );
    Abc_Print( -2, "\t-S str   : string representing the LUT structure [default = %s]\n", pPars->pLutStruct ? pPars->pLutStruct : "not used" );
    Abc_Print( -2, "\t-J str   : string representing the LUT structure (new method) [default = %s]\n", pPars->pLutStruct ? pPars->pLutStruct : "not used" );
    Abc_Print( -2, "\t-q       : toggles preprocessing using several starting points [default = %s]\n", pPars->fPreprocess? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fArea? "yes": "no" );
    Abc_Print( -2, "\t-r       : enables expansion/reduction of the best cuts [default = %s]\n", pPars->fExpRed? "yes": "no" );
    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", pPars->fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-e       : uses edge-based cut selection heuristics [default = %s]\n", pPars->fEdge? "yes": "no" );
    Abc_Print( -2, "\t-p       : uses power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-m       : enables cut minimization by removing vacuous variables [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles delay-oriented mapping used with -S <NN> [default = %s]\n", pPars->fDelayOptLut? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles deriving local AIGs using bi-decomposition [default = %s]\n", pPars->fBidec? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggles the use of one special feature [default = %s]\n", pPars->fUseBat? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles delay optimization by SOP balancing [default = %s]\n", pPars->fDelayOpt? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles delay optimization by DSD balancing [default = %s]\n", pPars->fDsdBalance? "yes": "no" );
    Abc_Print( -2, "\t-y       : toggles delay optimization with recorded library [default = %s]\n", pPars->fUserRecLib? "yes": "no" );
    Abc_Print( -2, "\t-u       : toggles delay optimization with SAT-based library [default = %s]\n", pPars->fUserSesLib? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles using buffers to decouple combinational outputs [default = %s]\n", pPars->fUseBuffs? "yes": "no" );
    //Abc_Print( -2, "\t-j       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck07? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles using cofactoring variables [default = %s]\n", pPars->fUseCofVars? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles matching based on precomputed DSD manager [default = %s]\n", pPars->fUseDsdTune? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles optimizing average rather than maximum level [default = %s]\n", pPars->fDoAverage? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggles computing DSDs of the cut functions [default = %s]\n", pPars->fUseDsd? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles computing truth tables in a new way [default = %s]\n", pPars->fUseTtPerm? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggles deriving LUTs when mapping into LUT structures [default = %s]\n", pPars->fDeriveLuts? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggles dumping truth tables into a binary file [default = %s]\n", pPars->fDumpFile? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIfif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkPerformIfif( Abc_Ntk_t * pNtk, Ifif_Par_t * pPars );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Ifif_Par_t Pars, * pPars = &Pars;
    int c, fError;

    pPars->nLutSize     =  -1;    // the LUT size
    pPars->pLutLib      = (If_LibLut_t *)Abc_FrameReadLibLut();       // the LUT library
    pPars->DelayWire    = (float)0.5;    // wire delay
    pPars->nDegree      =   0;    // structure degree
    pPars->fCascade     =   0;    // cascade
    pPars->fVerbose     =   0;    // verbose
    pPars->fVeryVerbose =   0;    // verbose

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "DNcvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayWire = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayWire < 0.0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nDegree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDegree < 0 )
                goto usage;
            break;
        case 'c':
            pPars->fCascade ^= 1;
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Need mapped network.\n" );
        return 1;
    }
    if ( pPars->pLutLib == NULL )
    {
        Abc_Print( -1, "LUT library is not given.\n" );
        return 1;
    }

    pPars->nLutSize = Abc_NtkGetFaninMax( pNtk );
    if ( pPars->nLutSize > pPars->pLutLib->LutMax )
    {
        Abc_Print( -1, "The max node size (%d) exceeds the LUT size (%d).\n", pPars->nLutSize, pPars->pLutLib->LutMax );
        return 1;
    }
    if ( pPars->nLutSize < pPars->pLutLib->LutMax )
        Abc_Print( 0, "Node size (%d) is less than LUT size (%d).\n", pPars->nLutSize, pPars->pLutLib->LutMax );
    // check delay information
    fError = 0;
    for ( c = 0; c < pPars->pLutLib->LutMax; c++ )
    {
        pPars->pLutDelays[c] = ( pPars->pLutLib->fVarPinDelays ? pPars->pLutLib->pLutDelays[pPars->pLutLib->LutMax][c] : pPars->pLutLib->pLutDelays[pPars->pLutLib->LutMax][0] );
        if ( pPars->DelayWire >= pPars->pLutDelays[c] )
        {
            fError = 1;
            printf(" Wire delay (%.2f) exceeds pin+wire delay (%.2f) for pin %d in the LUT library.\n", pPars->DelayWire, pPars->pLutDelays[c], c );
        }
    }
    if ( fError )
        return 1;

    // call the mapper
    Abc_NtkPerformIfif( pNtk, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: ifif [-DNcvwh]\n" );
    Abc_Print( -2, "\t           technology mapper into N-node K-LUT structures\n" );
    Abc_Print( -2, "\t           (takes a LUT network and maps it into a delay-optimal network\n" );
    Abc_Print( -2, "\t            of N-node K-LUT structures using the current LUT library)\n" );
    Abc_Print( -2, "\t-D float : wire delay (should be less than the LUT delay) [default = %.2f]\n", pPars->DelayWire );
    Abc_Print( -2, "\t-N num   : degree of the LUT structure [default = %d]\n", pPars->nDegree );
    Abc_Print( -2, "\t-c       : toggles using LUT cascade vs LUT cluster [default = %s]\n", pPars->fCascade? "cascade": "cluster" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
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
            Abc_Print( -1, "Strashing before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Converting into a seq AIG before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_NtkFpgaMapRetime( pNtkNew, nMaxIters, fVerbose );
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
    Abc_Print( -2, "usage: sfpga [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         performs integrated sequential FPGA mapping/retiming\n" );
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
int Abc_CommandAbc9False( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCheckFalse( Gia_Man_t * p, int nSlackMax, int nTimeOut, int fVerbose, int fVeryVerbose );
    Gia_Man_t * pTemp;
    int nSlackMax = 0;
    int nTimeOut = 0;
    int c, fVerbose = 0;
    int fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "STvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a char string.\n" );
                goto usage;
            }
            nSlackMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSlackMax < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a char string.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut < 0 )
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
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9False(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManCheckFalse( pAbc->pGia, nSlackMax, nTimeOut, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &false [-ST num] [-vwh]\n" );
    Abc_Print( -2, "\t         detecting and elimintation false paths\n" );
    Abc_Print( -2, "\t-S num : maximum slack to identify false paths [default = %d]\n",  nSlackMax );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n",   nTimeOut );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Flow( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPerformFlow( int fIsMapped, int nAnds, int nLevels, int nLutSize, int nCutNum, int fMinAve, int fUseMfs, int fVerbose );
    int nLutSize    =  6;
    int nCutNum     =  8;
    int fMinAve     =  0;
    int fUseMfs     =  0;
    int c, fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCtmvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 't':
            fMinAve ^= 1;
            break;
        case 'm':
            fUseMfs ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Flow(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManPerformFlow( Gia_ManHasMapping(pAbc->pGia), Gia_ManAndNum(pAbc->pGia), Gia_ManLevelNum(pAbc->pGia), nLutSize, nCutNum, fMinAve, fUseMfs, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &flow [-KC num] [-tmvh]\n" );
    Abc_Print( -2, "\t         integration optimization and mapping flow\n" );
    Abc_Print( -2, "\t-K num : the number of LUT inputs (LUT size) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-C num : the number of cuts at a node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-t     : toggle minimizing average rather than max delay [default = %s]\n", fMinAve? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using \"mfs2\" in the script [default = %s]\n", fUseMfs? "yes": "no" );
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
int Abc_CommandAbc9Flow2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPerformFlow2( int fIsMapped, int nAnds, int nLevels, int nLutSize, int nCutNum, int fBalance, int fMinAve, int fUseMfs, int fVerbose );
    int nLutSize    =  6;
    int nCutNum     =  8;
    int fBalance    =  0;
    int fMinAve     =  0;
    int fUseMfs     =  0;
    int c, fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCbtmvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'b':
            fBalance ^= 1;
            break;
        case 't':
            fMinAve ^= 1;
            break;
        case 'm':
            fUseMfs ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Flow2(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManPerformFlow2( Gia_ManHasMapping(pAbc->pGia), Gia_ManAndNum(pAbc->pGia), Gia_ManLevelNum(pAbc->pGia), nLutSize, nCutNum, fBalance, fMinAve, fUseMfs, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &flow2 [-KC num] [-btmvh]\n" );
    Abc_Print( -2, "\t         integration optimization and mapping flow\n" );
    Abc_Print( -2, "\t-K num : the number of LUT inputs (LUT size) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-C num : the number of cuts at a node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-b     : toggle using SOP balancing during synthesis [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle minimizing average (not maximum) level [default = %s]\n", fMinAve? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using \"mfs2\" in the script [default = %s]\n", fUseMfs? "yes": "no" );
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
int Abc_CommandAbc9Flow3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPerformFlow3( int nLutSize, int nCutNum, int fBalance, int fMinAve, int fUseMfs, int fUseLutLib, int fVerbose );
    int nLutSize    =  6;
    int nCutNum     =  8;
    int fBalance    =  0;
    int fMinAve     =  0;
    int fUseMfs     =  1;
    int fUseLutLib  =  0;
    int c, fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCbtmlvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'b':
            fBalance ^= 1;
            break;
        case 't':
            fMinAve ^= 1;
            break;
        case 'm':
            fUseMfs ^= 1;
            break;
        case 'l':
            fUseLutLib ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Flow3(): There is no AIG.\n" );
        return 1;
    }
    if ( fUseLutLib && Abc_FrameReadLibLut() == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Flow3(): Please enter LUT library using \'read_lut\'.\n" );
        return 1;
    }
    Gia_ManPerformFlow3( nLutSize, nCutNum, fBalance, fMinAve, fUseMfs, fUseLutLib, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &flow3 [-KC num] [-btmlvh]\n" );
    Abc_Print( -2, "\t         integration optimization and mapping flow\n" );
    Abc_Print( -2, "\t-K num : the number of LUT inputs (LUT size) [default = %d]\n",           nLutSize );
    Abc_Print( -2, "\t-C num : the number of cuts at a node [default = %d]\n",                  nCutNum );
    Abc_Print( -2, "\t-b     : toggle using SOP balancing during synthesis [default = %s]\n",   fBalance? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle minimizing average (not maximum) level [default = %s]\n", fMinAve? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using \"mfs2\" in the script [default = %s]\n",           fUseMfs? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle using previously entered LUT library [default = %s]\n",   fUseLutLib? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",           fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9If( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[200];
    char LutSize[200];
    Gia_Man_t * pNew;
    If_Par_t Pars, * pPars = &Pars;
    int c;
    // set defaults
    Gia_ManSetIfParsDefault( pPars );
    if ( Abc_FrameReadLibLut() == NULL )
    {
        Abc_Print( -1, "LUT library is not given. Using default LUT library.\n" );
        Abc_FrameSetLibLut( If_LibLutSetSimple( 6 ) );
    }
    pPars->pLutLib = (If_LibLut_t *)Abc_FrameReadLibLut();
    pPars->pCellLib = (If_LibCell_t *)Abc_FrameReadLibCell();
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFAGRDEWSJTXYZMqalepmrsdbgxyofuijkztncvwh" ) ) != EOF )
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
            if ( pPars->nLutSize < 0 )
                goto usage;
            // if the LUT size is specified, disable library
            pPars->pLutLib = NULL;
            pPars->pCellLib = NULL;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlowIters < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaIters < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a positive integer no less than 3.\n" );
                goto usage;
            }
            pPars->nGateSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGateSize < 2 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
                return 0;
            }
            pPars->nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRelaxRatio < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nStructType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStructType < 0 || pPars->nStructType > 2 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nAndDelay = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAndArea < 0 )
                goto usage;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by a positive integer 0,1,or 2.\n" );
                goto usage;
            }
            pPars->nAndArea = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAndDelay < 0 )
                goto usage;
            break;
        case 'M':
        {
            int Value;
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by 0 or 1.\n" );
                goto usage;
            }
            Value = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Value < 0 || Value > 1 )
                goto usage;
            pPars->fDelayOptCell = Value;
            break;
        }
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->Epsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Epsilon < 0.0 || pPars->Epsilon > 1.0 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->WireDelay = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->WireDelay < 0.0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by string.\n" );
                goto usage;
            }
            pPars->pLutStruct = argv[globalUtilOptind];
            globalUtilOptind++;
            if ( strlen(pPars->pLutStruct) != 2 && strlen(pPars->pLutStruct) != 3 )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a 2- or 3-char string (e.g. \"44\" or \"555\").\n" );
                goto usage;
            }
            break;
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by string.\n" );
                goto usage;
            }
            pPars->pLutStruct = argv[globalUtilOptind];
            pPars->fEnableStructN = 1;
            globalUtilOptind++;
            if ( strlen(pPars->pLutStruct) != 2 )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by a 2-char string (e.g. \"44\" or \"55\").\n" );
                goto usage;
            }
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by a positive integer 3, 4, 5, or 6.\n" );
                goto usage;
            }
            pPars->nLutDecSize = atoi(argv[globalUtilOptind]);
            pPars->fUserLutDec = 1;
            globalUtilOptind++;
            if ( pPars->nLutDecSize < 3 || pPars->nLutDecSize > 6 )
                goto usage;
            break;
        case 'q':
            pPars->fPreprocess ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'r':
            pPars->fExpRed ^= 1;
            break;
        case 'l':
            pPars->fLut6Filter ^= 1;
            break;
        case 'e':
            pPars->fEdge ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 's':
            pPars->fDelayOptLut ^= 1;
            break;
        case 'd':
            pPars->fUse34Spec ^= 1;
            break;
        case 'b':
            //pPars->fUseBat ^= 1;
            pPars->fUseCheck1 ^= 1;
            break;
        case 'g':
            pPars->fDelayOpt ^= 1;
            break;
        case 'x':
            pPars->fDsdBalance ^= 1;
            break;
        case 'y':
            pPars->fUserRecLib ^= 1;
            break;
        case 'o':
            pPars->fUseBuffs ^= 1;
            break;
        case 'f':
            pPars->fEnableCheck75 ^= 1;
            break;
        case 'u':
            pPars->fEnableCheck75u ^= 1;
            break;
        case 'i':
            //pPars->fUseCofVars ^= 1;
            pPars->fUseCheck2 ^= 1;
            break;
        case 'j':
            pPars->fEnableCheck07 ^= 1;
            break;
        //case 'j':
        //    pPars->fUseAndVars ^= 1;
        //    break;
        case 'k':
            pPars->fUseDsdTune ^= 1;
            break;
        case 'z':
            pPars->fDeriveLuts ^= 1;
            break;
        case 't':
            pPars->fDoAverage ^= 1;
            break;
        case 'n':
            pPars->fUseDsd ^= 1;
            break;
        case 'c':
            pPars->fUseTtPerm ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVerboseTrace ^= 1;
            break;
        case 'h':
            pPars->fHashMapping ^= 1;
            break;
        default:
            goto usage;
        }
    }

    // LMS defaults to six-input cuts unless the user supplied -K.
    if ( pPars->fUserRecLib && pPars->nLutSize == -1 )
    {
        pPars->nLutSize = 6;
        pPars->pLutLib = NULL;
        pPars->pCellLib = NULL;
    }

    // Auto-detect K from cell library when -j is used
    if ( pPars->fEnableCheck07 && pPars->nLutSize == -1 )
    {
        If_LibCell_t * pCellLib = (If_LibCell_t *)Abc_FrameReadLibCell();
        if ( pCellLib )
        {
            int nMaxInputs = If_LibCellGetMaxInputs( pCellLib );
            if ( nMaxInputs > 0 )
            {
                pPars->nLutSize = nMaxInputs;
                if ( pPars->fVerbose )
                    Abc_Print( 1, "Auto-detected K=%d from cell library (max inputs).\n", nMaxInputs );
                // Disable LUT library since we're using K from cell library
                pPars->pLutLib = NULL;
                pPars->pCellLib = pCellLib;
            }
        }
    }

    if ( pAbc->pGia == NULL )
    {
        if ( !Abc_FrameReadFlag("silentmode") )
        Abc_Print( -1, "Empty GIA network.\n" );
        return 0;
    }
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "This command does not work with barrier buffers.\n" );
        return 1;
    }
    if ( Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has mapping. Run \"&st\".\n" );
        return 1;
    }

    // Use the LUT library for an unspecified cut size.
    if ( pPars->nLutSize == -1 )
    {
        if ( pPars->pLutLib == NULL )
        {
            Abc_Print( -1, "The LUT library is not given.\n" );
            return 1;
        }
        // get LUT size from the library
        pPars->nLutSize = pPars->pLutLib->LutMax;
        // if variable pin delay, force truth table computation
//        if ( pPars->pLutLib->fVarPinDelays )
//            pPars->fTruth = 1;
    }

    if ( pPars->nLutSize < 2 || pPars->nLutSize > IF_MAX_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", pPars->nLutSize );
        return 1;
    }

    if ( pPars->nCutsMax < 1 || pPars->nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    if ( !Gia_ManHasChoices(pAbc->pGia) && pAbc->pGia->pNexts && Gia_ManHasDangling(pAbc->pGia) )
    {
        Abc_Print( -1, "Choice nodes are not in the format required by &if. Use \"&get -s\" to import choices for mapping.\n" );
        return 1;
    }

    // enable truth table computation if choices are selected
    if ( Gia_ManHasChoices(pAbc->pGia) )
    {
//        if ( !Abc_FrameReadFlag("silentmode") )
//            Abc_Print( 0, "Performing LUT mapping with choices.\n" );
        pPars->fExpRed = 0;
    }

    if ( pPars->fUseBat )
    {
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature only works for {4,5,6}-LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
    }

    if ( pPars->fEnableCheck07 + pPars->fUseCofVars + pPars->fUseDsdTune + pPars->fEnableCheck75 + pPars->fEnableCheck75u + (pPars->pLutStruct != NULL) > 1 )
    {
        Abc_Print( -1, "Only one additional check can be performed at the same time.\n" );
        return 1;
    }
    if ( pPars->fEnableCheck07 )
    {
        if ( pPars->nLutSize > 9 )
        {
            Abc_Print( -1, "This feature only works for up to 9-input LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheckJ;
        pPars->fCutMin = 1;
    }
    if ( pPars->fUseCheck1 || pPars->fUseCheck2 )
    {
        if ( pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature only works for no more than 6-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = pPars->fUseCheck2 ? If_MatchCheck2 : If_MatchCheck1;
        pPars->fCutMin = 1;
    }
    if ( pPars->fUseCofVars )
    {
        if ( !(pPars->nLutSize & 1) )
        {
            Abc_Print( -1, "This feature only works for odd-sized LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
    }
    if ( pPars->fUseAndVars )
        pPars->fCutMin = 1;
    if ( pPars->fUseDsdTune )
    {
        If_DsdMan_t * pDsdMan = (If_DsdMan_t *)Abc_FrameReadManDsd();
        if ( pDsdMan == NULL )
        {
            Abc_Print( -1, "DSD manager is not available.\n" );
            return 1;
        }
        if ( pPars->nLutSize > If_DsdManVarNum(pDsdMan) )
        {
            Abc_Print( -1, "LUT size (%d) is more than the number of variables in the DSD manager (%d).\n", pPars->nLutSize, If_DsdManVarNum(pDsdMan) );
            return 1;
        }
        if ( pPars->fDeriveLuts && If_DsdManGetCellStr(pDsdMan) == NULL )
        {
            Abc_Print( -1, "DSD manager is not matched with any particular cell.\n" );
            return 1;
        }
        pPars->fCutMin = 1;
        pPars->fUseDsd = 1;
        If_DsdManSetNewAsUseless( pDsdMan );
    }
    if ( pPars->fEnableCheck75 || pPars->fEnableCheck75u )
    {
        if ( pPars->fEnableCheck75 && pPars->fEnableCheck75u )
        {
            Abc_Print( -1, "Switches -f and -u are not compatible.\n" );
            return 1;
        }
        if ( pPars->nLutSize < 5 || pPars->nLutSize > 8 )
        {
            Abc_Print( -1, "This feature only works for {6,7,8}-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheck75;
        pPars->fCutMin = 1;
    }
    if ( pPars->pLutStruct )
    {
        if ( pPars->fDsdBalance )
        {
            Abc_Print( -1, "Incompatible options (-S and -x).\n" );
            return 1;
        }
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 16 )
        {
            Abc_Print( -1, "This feature only works for [6;16]-LUTs.\n" );
            return 1;
        }
        if ( pPars->fEnableStructN )
        {
            pPars->pFuncCell = pPars->fDelayOptLut ? NULL : If_CutPerformCheckXX;
        }
        else
        {
            pPars->pFuncCell = pPars->fDelayOptLut ? NULL : If_CutPerformCheck16;
        }
        pPars->fCutMin = 1;
        pPars->nLutDecSize = pPars->pLutStruct[0] - '0';
    }

    if ( pPars->fUserLutDec )
    {
        if ( pPars->nLutDecSize == 0 )
        {
            Abc_Print( -1, "LUT decomposition size (%d) must be set.\n", pPars->nLutDecSize );
            return 1;
        }
        if ( pPars->nLutDecSize >= pPars->nLutSize )
        {
            Abc_Print( -1, "LUT size (%d) must be greater than the LUT decomposition size (%d).\n", pPars->nLutSize, pPars->nLutDecSize );
            return 1;
        }
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 11 )
        {
            Abc_Print( -1, "This feature only works for [4;11]-LUTs.\n" );
            return 1;
        }
    }

    if ( pPars->fUse34Spec )
    {
        pPars->fTruth    = 1;
        pPars->fCutMin   = 1;
        pPars->nLutSize  = 4;
    }

    if ( pPars->fEnableCheck07 )
        pPars->nCutsMax = Abc_MaxInt( pPars->nCutsMax, 16 );
    else
        pPars->pCellLib = NULL;

    // enable truth table computation if cut minimization is selected
    if ( pPars->fCutMin || pPars->fDeriveLuts )
    {
        pPars->fTruth = 1;
        pPars->fExpRed = 0;
        if ( pPars->pLutStruct == NULL && !pPars->fUseDsdTune )
            pPars->fDeriveLuts = 1;
    }
    // modify the subgraph recording
    if ( pPars->fUserRecLib )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
    }
    // modify for delay optimization
    if ( pPars->fDelayOpt || pPars->fDsdBalance || pPars->fDelayOptLut || pPars->fUserLutDec )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUseDsd     =  pPars->fDsdBalance || pPars->fDelayOptLut;
        pPars->pLutLib     =  NULL;
    }
    // modify for delay optimization
    if ( pPars->nGateSize > 0 )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
        pPars->nLutSize    =  pPars->nGateSize;
    }

    if ( pPars->fUseDsd || pPars->fUseTtPerm || pPars->fLut6Filter )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fExpRed     =  0;
    }

    if ( pPars->fUseDsd )
    {
        int LutSize = (pPars->pLutStruct && pPars->pLutStruct[2] == 0)? pPars->pLutStruct[0] - '0' : 0;
        If_DsdMan_t * p = (If_DsdMan_t *)Abc_FrameReadManDsd();
        if ( pPars->pLutStruct && pPars->pLutStruct[2] != 0 )
        {
            printf( "DSD only works for LUT structures XY.\n" );
            return 0;
        }
        if ( p && pPars->nLutSize > If_DsdManVarNum(p) )
        {
            printf( "DSD manager has incompatible number of variables.\n" );
            return 0;
        }
        if ( p && LutSize != If_DsdManLutSize(p) && !pPars->fDsdBalance )
        {
            printf( "DSD manager has different LUT size.\n" );
            return 0;
        }
        if ( p == NULL )
        {
            if ( LutSize > DAU_MAX_VAR || pPars->nLutSize > DAU_MAX_VAR )
            {
                printf( "Size of required DSD manager (%d) exceeds the precompiled limit (%d) (change parameter DAU_MAX_VAR).\n", LutSize, DAU_MAX_VAR );
                return 0;
            }
            Abc_FrameSetManDsd( If_DsdManAlloc(pPars->nLutSize, LutSize) );
        }
    }

    if ( pPars->fUserRecLib )
    {
        if ( !Abc_NtkRecIsRunning3() )
        {
            extern int Abc_NtkRecStartBuiltin3( FILE * pOut, FILE * pError );
            if ( pPars->nLutSize != 6 )
            {
                Abc_Print(-1, "Built-in LMS library has 6 inputs, but the selected cut size is %d. Use -K 6 or load a matching external LMS library.\n", pPars->nLutSize);
                return 0;
            }
            if ( !Abc_NtkRecStartBuiltin3(Abc_FrameReadOut(pAbc), Abc_FrameReadErr(pAbc)) ) return 1;
        }
        if ( Abc_NtkRecInputNum3() != pPars->nLutSize )
        {
            printf( "The number of library inputs (%d) different from the K parameters (%d).\n", Abc_NtkRecInputNum3(), pPars->nLutSize );
            return 0;
        }
    }

    // complain if truth tables are requested but the cut size is too large
    if ( pPars->fTruth && pPars->nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Truth tables cannot be computed for LUT larger than %d inputs.\n", IF_MAX_FUNC_LUTSIZE );
        return 1;
    }
    if ( pAbc->pGia->pManTime && pAbc->pLibBox == NULL )
    {
        Abc_Print( -1, "Design has boxes but box library is not entered.\n" );
        return 1;
    }

    // add wire delay to LUT library delays
    if ( pPars->WireDelay > 0 && pPars->pLutLib )
    {
        int i, k;
        for ( i = 0; i <= pPars->pLutLib->LutMax; i++ )
            for ( k = 0; k <= i; k++ )
                pPars->pLutLib->pLutDelays[i][k] += pPars->WireDelay;
    }
    // perform mapping
    pNew = Gia_ManPerformMapping( pAbc->pGia, pPars );
    // subtract wire delay from LUT library delays
    if ( pPars->WireDelay > 0 && pPars->pLutLib )
    {
        int i, k;
        for ( i = 0; i <= pPars->pLutLib->LutMax; i++ )
            for ( k = 0; k <= i; k++ )
                pPars->pLutLib->pLutDelays[i][k] -= pPars->WireDelay;
    }
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9If(): Mapping of GIA has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%.2f", pPars->DelayTarget );
    if ( pPars->nLutSize == -1 )
        sprintf(LutSize, "%s", pPars->fUserRecLib ? "6" : "library" );
    else
        sprintf(LutSize, "%d", pPars->nLutSize );
    Abc_Print( -2, "usage: &if [-KCFAGRTXYZM num] [-DEW float] [-SJ str] [-qarlepmsdbgxyofuijkztnchvw]\n" );
    Abc_Print( -2, "\t           performs FPGA technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < %d) [default = %s]\n", IF_MAX_LUTSIZE+1, LutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (0 < num < 2^12) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : the number of area flow recovery iterations (num >= 0) [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations (num >= 0) [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-G num   : the max AND/OR gate size for mapping (0 = unused) [default = %d]\n", pPars->nGateSize );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n", pPars->nRelaxRatio );
    Abc_Print( -2, "\t-T num   : the type of LUT structures [default = any]\n", pPars->nStructType );
    Abc_Print( -2, "\t-X num   : delay of AND-gate in LUT library units [default = %d]\n", pPars->nAndDelay );
    Abc_Print( -2, "\t-Y num   : area of AND-gate in LUT library units [default = %d]\n", pPars->nAndArea );
    Abc_Print( -2, "\t-M num   : enables delay-driven decomposition [default = %d]\n", pPars->fDelayOptCell );
    Abc_Print( -2, "\t-D float : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->Epsilon );
    Abc_Print( -2, "\t-W float : sets wire delay between adjects LUTs [default = %f]\n", pPars->WireDelay );
    Abc_Print( -2, "\t-S str   : string representing the LUT structure [default = %s]\n", pPars->pLutStruct ? pPars->pLutStruct : "not used" );
    Abc_Print( -2, "\t-J str   : string representing the LUT structure [default = %s]\n", pPars->pLutStruct ? pPars->pLutStruct : "not used" );
    Abc_Print( -2, "\t-Z num   : the number of LUT inputs for delay-driven LUT decomposition [default = not used]\n" );
    Abc_Print( -2, "\t-q       : toggles preprocessing using several starting points [default = %s]\n", pPars->fPreprocess? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fArea? "yes": "no" );
    Abc_Print( -2, "\t-r       : enables expansion/reduction of the best cuts [default = %s]\n", pPars->fExpRed? "yes": "no" );
//    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", pPars->fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggle restricting the type of 6-input lookup tables [default = %s]\n", pPars->fLut6Filter? "yes": "no" );
    Abc_Print( -2, "\t-e       : uses edge-based cut selection heuristics [default = %s]\n", pPars->fEdge? "yes": "no" );
    Abc_Print( -2, "\t-p       : uses power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-m       : enables cut minimization by removing vacuous variables [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles delay-oriented mapping used with -S <NN> [default = %s]\n", pPars->fDelayOptLut? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles deriving specialized matching step [default = %s]\n", pPars->fUse34Spec? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggles the use of one special feature [default = %s]\n", pPars->fUseBat? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles delay optimization by SOP balancing [default = %s]\n", pPars->fDelayOpt? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles delay optimization by DSD balancing [default = %s]\n", pPars->fDsdBalance? "yes": "no" );
    Abc_Print( -2, "\t-y       : toggles delay optimization with recorded library [default = %s]\n", pPars->fUserRecLib? "yes": "no" );
    Abc_Print( -2, "\t           -y uses the built-in six-input library if none is loaded; exact cache is on\n" );
    Abc_Print( -2, "\t           -y defaults to -K 6; an explicit -K overrides this default\n" );
    Abc_Print( -2, "\t-o       : toggles using buffers to decouple combinational outputs [default = %s]\n", pPars->fUseBuffs? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck75? "yes": "no" );
    Abc_Print( -2, "\t-u       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck75u? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles using cofactoring variables [default = %s]\n", pPars->fUseCofVars? "yes": "no" );
    Abc_Print( -2, "\t-j       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck07? "yes": "no" );
//    Abc_Print( -2, "\t-j       : toggles using AND bi-decomposition [default = %s]\n", pPars->fUseAndVars? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles matching based on precomputed DSD manager [default = %s]\n", pPars->fUseDsdTune? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggles deriving LUTs when mapping into LUT structures [default = %s]\n", pPars->fDeriveLuts? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles optimizing average rather than maximum level [default = %s]\n", pPars->fDoAverage? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggles computing DSDs of the cut functions [default = %s]\n", pPars->fUseDsd? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles computing truth tables in a new way [default = %s]\n", pPars->fUseTtPerm? "yes": "no" );
    Abc_Print( -2, "\t-h       : toggles rehashing AIG after mapping [default = %s]\n", pPars->fHashMapping? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles printing delay trace [default = %s]\n", pPars->fVerboseTrace? "yes": "no" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Iff( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManIffTest( Gia_Man_t * pGia, If_LibLut_t * pLib, int fVerbose );
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
        Abc_Print( -1, "Abc_CommandAbc9Iff(): There is no AIG to map.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iff(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    if ( Abc_FrameReadLibLut() == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iff(): LUT library is not defined.\n" );
        return 1;
    }
    Gia_ManIffTest( pAbc->pGia, (If_LibLut_t *)Abc_FrameReadLibLut(), fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &iff [-vh]\n" );
    Abc_Print( -2, "\t           performs structural mapping into LUT structures\n" );
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
int Abc_CommandAbc9Iiff( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManIiffTest( char * pFileName, Gia_Man_t * pGia, int nLutSize, int nNumCuts, int fUseGates, int fUseCells, int fUseLuts, int fVerbose );
    char * pFileName = NULL;
    int nLutSize     =  8;
    int nNumCuts     = 12;
    int fUseGates    =  0;
    int fUseCells    =  0;
    int fUseLuts     =  0;
    int c, fVerbose  =  0;
    Gia_Man_t * pNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCgclvh" ) ) != EOF )
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
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nNumCuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'g':
            fUseGates ^= 1;
            break;
        case 'c':
            fUseCells ^= 1;
            break;
        case 'l':
            fUseLuts ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iiff(): There is no AIG to map.\n" );
        return 1;
    }
    pNew = Gia_ManIiffTest( pFileName, pAbc->pGia, nLutSize, nNumCuts, fUseGates, fUseCells, fUseLuts, fVerbose );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iiff(): Mapping has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &iiff [-KC num] [-gclvh] <file>\n" );
    Abc_Print( -2, "\t           performs techology mapping\n" );
    Abc_Print( -2, "\t-K num   : the maximum LUT size [default = %d]\n",  nLutSize );
    Abc_Print( -2, "\t-C num   : the maximum cut count [default = %d]\n", nNumCuts );
    Abc_Print( -2, "\t-g       : toggle using gates [default = %s]\n",    fUseGates? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle using cells [default = %s]\n",    fUseCells? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggle using LUTs  [default = %s]\n",    fUseLuts? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<file>   : (optional) output file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9If2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    If2_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew;
    char * pEnd;
    long Value;
    double Delay;
    int c;
    If2_ManSetDefaultPars( pPars );
    // Choices benefit from one extra priority cut and support minimization.
    // Ordinary AIGs retain the compact structural defaults.
    if ( pAbc->pGia && Gia_ManHasChoices(pAbc->pGia) )
    {
        pPars->nCutsMax = 4;
        pPars->fCutMin = 1;
    }
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KCFADmadvh")) != EOF )
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
                if ( Value < 1 || Value > 32 ) goto usage;
                pPars->nCutsMax = (int)Value;
            }
            else if ( c == 'F' ) pPars->nFlowIters = (int)Value;
            else pPars->nAreaIters = (int)Value;
            break;
        case 'D':
            if ( globalUtilOptind >= argc ) goto usage;
            Delay = strtod( argv[globalUtilOptind], &pEnd );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || !(Delay > 0 && Delay < 1.0e10) ) goto usage;
            globalUtilOptind++;
            pPars->DelayTarget = (float)Delay;
            break;
        case 'm': pPars->fCutMin ^= 1; break;
        case 'a': pPars->fArea ^= 1; break;
        case 'd': pPars->fDiverse ^= 1; break;
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
    pNew = If2_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9If2(): LUT mapping has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &if2 [-KCFA num] [-D float] [-madvh]\n" );
    Abc_Print( -2, "\t           performs compact LUT mapping directly on the GIA\n" );
    Abc_Print( -2, "\t           choice inputs default to four cuts and support minimization; -m disables it\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 <= num <= 6) [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the maximum number of nontrivial cuts (1 <= num <= 32) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : the number of area flow rounds after initialization [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-D float : sets the mapping delay constraint [default = best found]\n" );
    Abc_Print( -2, "\t-m       : toggles truth-table cuts and support minimization [default = %s]\n", pPars->fCutMin ? "yes" : "no" );
    Abc_Print( -2, "\t-a       : toggles area-only mapping [default = %s]\n", pPars->fArea ? "yes" : "no" );
    Abc_Print( -2, "\t-d       : toggles retaining a delay alternative [default = %s]\n", pPars->fDiverse ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9If3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    If3_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew;
    char * pEnd;
    long Value;
    double Delay;
    int c;
    If3_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KCFARDmadrspvh")) != EOF )
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
                if ( Value < 1 || Value > 32 ) goto usage;
                pPars->nCutsMax = (int)Value;
            }
            else if ( c == 'F' ) pPars->nFlowIters = (int)Value;
            else if ( c == 'A' ) pPars->nAreaIters = (int)Value;
            else pPars->nExploreIters = (int)Value;
            break;
        case 'D':
            if ( globalUtilOptind >= argc ) goto usage;
            Delay = strtod( argv[globalUtilOptind], &pEnd );
            if ( pEnd == argv[globalUtilOptind] || *pEnd || !(Delay > 0 && Delay < 1.0e10) ) goto usage;
            globalUtilOptind++;
            pPars->DelayTarget = (float)Delay;
            break;
        case 'm': pPars->fCutMin ^= 1; break;
        case 'a': pPars->fArea ^= 1; break;
        case 'd': pPars->fDiverse ^= 1; break;
        case 'r': pPars->fReverse ^= 1; break;
        case 's': pPars->fSynthesis ^= 1; break;
        case 'p': pPars->fPack ^= 1; break;
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
    pNew = If3_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9If3(): LUT mapping has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &if3 [-KCFAR num] [-D float] [-madrspvh]\n" );
    Abc_Print( -2, "\t           performs delay-constrained LUT area recovery on the GIA\n" );
    Abc_Print( -2, "\t           uses construction-proved alternatives and LUT-directed resynthesis\n" );
    Abc_Print( -2, "\t           selected covers may be remapped with 12 cuts and one recovery round\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 <= num <= 6) [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : initial mapping cut limit (1 <= num <= 32) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : initial mapping area flow rounds [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : initial mapping exact area recovery rounds [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-R num   : the number of causal sharing recovery rounds [default = %d]\n", pPars->nExploreIters );
    Abc_Print( -2, "\t-D float : sets the mapping delay constraint [default = best found]\n" );
    Abc_Print( -2, "\t-m       : toggles truth-table cuts and support minimization [default = %s]\n", pPars->fCutMin ? "yes" : "no" );
    Abc_Print( -2, "\t-a       : toggles area-only mapping [default = %s]\n", pPars->fArea ? "yes" : "no" );
    Abc_Print( -2, "\t-d       : toggles retaining a delay alternative [default = %s]\n", pPars->fDiverse ? "yes" : "no" );
    Abc_Print( -2, "\t-r       : toggles reverse exact-area recovery [default = %s]\n", pPars->fReverse ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggles synthesis alternatives for plain AIGs [default = %s]\n", pPars->fSynthesis ? "yes" : "no" );
    Abc_Print( -2, "\t-p       : toggles LUT-network resynthesis [default = %s]\n", pPars->fPack ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs the legacy MPM mapping command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9If2Old( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Mpm_ManCellMapping( Gia_Man_t * p, Mpm_Par_t * pPars, void * pMio );
    extern Gia_Man_t * Mpm_ManLutMapping( Gia_Man_t * p, Mpm_Par_t * pPars );
    char Buffer[200];
    Abc_Ntk_t * pTemp;
    Gia_Man_t * pNew;
    Mpm_Par_t Pars, * pPars = &Pars;
    int c, nLutSize = 6;
    // set defaults
    Mpm_ManSetParsDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCDtmzrcuxvwh" ) ) != EOF )
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
            if ( nLutSize < 2 || nLutSize > 16 )
            {
                Abc_Print( -1, "LUT size %d is not supported.\n", nLutSize );
                goto usage;
            }
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nNumCuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNumCuts < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
                goto usage;
            break;
        case 't':
            pPars->fUseGates ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'z':
            pPars->fDeriveLuts ^= 1;
            break;
        case 'r':
            pPars->fOneRound ^= 1;
            break;
        case 'c':
            pPars->fMap4Cnf ^= 1;
            break;
        case 'u':
            pPars->fMap4Aig ^= 1;
            break;
        case 'x':
            pPars->fMap4Gates ^= 1;
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

    if ( pPars->fMap4Cnf )
        pPars->fUseDsd = 1;
    if ( pPars->fCutMin )
        pPars->fUseDsd = 1;
//        pPars->fUseTruth = 1;
    if ( pPars->fMap4Gates )
    {
        pPars->fUseDsd = 1;
        if ( pAbc->pLibScl == NULL )
        {
            Abc_Print( -1, "There is no SCL library available.\n" );
            return 1;
        }
        pPars->pScl = pAbc->pLibScl;
    }
    if ( pPars->fUseDsd || pPars->fUseTruth )
        pPars->fDeriveLuts = 1;
    if ( pPars->fUseDsd && nLutSize != 6 )
    {
        Abc_Print( -1, "Currently DSD can only be used with 6-input cuts.\n" );
        return 1;
    }
    // perform mapping
    assert( pPars->pLib == NULL );
    if ( pPars->fMap4Gates )
    {
        if ( Abc_FrameReadLibGen() == NULL )
        {
            Abc_Print( -1, "There is no GENLIB library available.\n" );
            return 1;
        }
        pPars->pLib = Mpm_LibLutSetSimple( nLutSize );
        pTemp = Mpm_ManCellMapping( pAbc->pGia, pPars, Abc_FrameReadLibGen() );
        Mpm_LibLutFree( pPars->pLib );
        if ( pTemp == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9If2Old(): Mapping into standard cells has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pTemp );
    }
    else
    {
        pPars->pLib = Mpm_LibLutSetSimple( nLutSize );
        pNew = Mpm_ManLutMapping( pAbc->pGia, pPars );
        Mpm_LibLutFree( pPars->pLib );
        if ( pNew == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9If2Old(): Mapping into LUTs has failed.\n" );
            return 1;
        }
        Abc_FrameUpdateGia( pAbc, pNew );
    }
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &if2old [-KCD num] [-tmzrcuxvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : sets the LUT size for the mapping [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (0 < num < 2^12) [default = %d]\n", pPars->nNumCuts );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-t       : enables using AND/XOR/MUX nodes instead of simple AIG [default = %s]\n", pPars->fUseGates? "yes": "no" );
    Abc_Print( -2, "\t-m       : enables cut minimization by removing vacuous variables [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggles deriving LUTs when mapping into LUT structures [default = %s]\n", pPars->fDeriveLuts? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggles using one round of mapping [default = %s]\n", pPars->fOneRound? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles mapping for CNF computation [default = %s]\n", pPars->fMap4Cnf? "yes": "no" );
    Abc_Print( -2, "\t-u       : toggles mapping for AIG computation [default = %s]\n", pPars->fMap4Aig? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles mapping for standard cells [default = %s]\n", pPars->fMap4Gates? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManSifPerform( Gia_Man_t * p, int nLutSize, int fEvalOnly, int fVerbose );
    Gia_Man_t * pNew;
    int c, nLutSize = 6, fEvalOnly = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kevh" ) ) != EOF )
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
            if ( nLutSize < 2 || nLutSize > 16 )
            {
                Abc_Print( -1, "LUT size %d is not supported.\n", nLutSize );
                goto usage;
            }
            break;
        case 'e':
            fEvalOnly ^= 1;
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
    pNew = Gia_ManSifPerform( pAbc->pGia, nLutSize, fEvalOnly, fVerbose );
    if ( pNew != NULL )
        Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &sif [-K num] [-evh]\n" );
    Abc_Print( -2, "\t           performs technology mapping\n" );
    Abc_Print( -2, "\t-K num   : sets the LUT size for the mapping [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-e       : toggles the evaluation mode [default = %s]\n", fEvalOnly? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Jf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Jf_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCDWaekmdcgvwh" ) ) != EOF )
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
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
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
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'e':
            pPars->fOptEdge ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'd':
            pPars->fFuncDsd ^= 1;
            break;
        case 'c':
            pPars->fGenCnf ^= 1;
            break;
        case 'g':
            pPars->fPureAig ^= 1;
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
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Jf(): This command does not work with barrier buffers.\n" );
        return 1;
    }
    if ( (pPars->fFuncDsd || pPars->fGenCnf) && pPars->nLutSize > 6 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Jf(): DSD computation works for LUT6 or less.\n" );
        return 1;
    }

    if ( (pPars->fFuncDsd || pPars->fGenCnf) && !Sdm_ManCanRead() )
    {
        Abc_Print( -1, "Abc_CommandAbc9Jf(): Cannot input DSD data from file.\n" );
        return 1;
    }

    pNew = Jf_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Jf(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &jf [-KCDW num] [-akmdcgvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-W num   : min frequency when printing functions with \"-w\" [default = %d]\n", pPars->nVerbLimit );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggles edge vs node minimization [default = %s]\n", pPars->fOptEdge? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n", pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles using DSD to represent cut functions [default = %s]\n", pPars->fFuncDsd? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles mapping for CNF generation [default = %s]\n", pPars->fGenCnf? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles generating AIG without mapping [default = %s]\n", pPars->fPureAig? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Kf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Kf_ManSetDefaultPars( Jf_Par_t * pPars );
    extern Gia_Man_t * Kf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars );
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Kf_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCPDWaekmdcgtsvwh" ) ) != EOF )
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
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nProcNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nProcNum < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
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
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'e':
            pPars->fOptEdge ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'd':
            pPars->fFuncDsd ^= 1;
            break;
        case 'c':
            pPars->fGenCnf ^= 1;
            break;
        case 'g':
            pPars->fPureAig ^= 1;
            break;
        case 't':
            pPars->fCutHashing ^= 1;
            break;
        case 's':
            pPars->fCutSimple ^= 1;
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

    pNew = Kf_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Kf(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &kf [-KCPDW num] [-akmdcgtsvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-P num   : the number of cut computation processes (0 <= P <= %d) [default = %d]\n", pPars->nProcNumMax, pPars->nProcNum );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-W num   : min frequency when printing functions with \"-w\" [default = %d]\n", pPars->nVerbLimit );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggles edge vs node minimization [default = %s]\n", pPars->fOptEdge? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n", pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles using DSD to represent cut functions [default = %s]\n", pPars->fFuncDsd? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles mapping for CNF generation [default = %s]\n", pPars->fGenCnf? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles generating AIG without mapping [default = %s]\n", pPars->fPureAig? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles cut computation using hash table [default = %s]\n", pPars->fCutHashing? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles cut computation using a simple method [default = %s]\n", pPars->fCutSimple? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Lf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Lf_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFARLEDWMekmupstgvwh" ) ) != EOF )
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
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
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
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
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nLutSizeMux = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSizeMux < 2 || pPars->nLutSizeMux > pPars->nLutSizeMax )
            {
                Abc_Print( -1, "LUT size %d is not supported.\n", pPars->nLutSizeMux );
                goto usage;
            }
            break;
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'e':
            pPars->fOptEdge ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'u':
            pPars->fUseMux7 ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 's':
            pPars->fPureAig ^= 1;
            break;
        case 't':
            pPars->fDoAverage ^= 1;
            break;
        case 'g':
            pPars->fCutGroup ^= 1;
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
    if ( Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has mapping. Run \"&st\".\n" );
        return 1;
    }
    if ( pPars->nLutSizeMux && pPars->fUseMux7 )
    {
        Abc_Print( -1, "Flags \"-M\" and \"-u\" are incompatible.\n" );
        return 1;
    }
    if ( pPars->fCutGroup )
    {
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature works only for LUT size equal to 4, 5, and 6.\n" );
            return 1;
        }
        printf( "Using cut grouping for %d-LUTs. Considering cuts up to %d.\n", pPars->nLutSize, 2*pPars->nLutSize + 1 );
        pPars->nLutSize = 2*pPars->nLutSize + 1;
    }
    pNew = Lf_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Lf(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &lf [-KCFARLEDM num] [-kmupstgvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : the number of area flow rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-A num   : the number of exact area rounds [default = %d]\n", pPars->nRoundsEla );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n", pPars->nRelaxRatio );
    Abc_Print( -2, "\t-L num   : the fanout limit for coarsening XOR/MUX (num >= 2) [default = %d]\n", pPars->nCoarseLimit );
    Abc_Print( -2, "\t-E num   : the area/edge tradeoff parameter (0 <= num <= 100) [default = %d]\n", pPars->nAreaTuner );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-M num   : LUT size when cofactoring is performed (0 <= num <= 100) [default = %d]\n", pPars->nLutSizeMux );
//    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggles edge vs node minimization [default = %s]\n", pPars->fOptEdge? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n", pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-u       : toggles using additional MUXes [default = %s]\n", pPars->fUseMux7? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggles power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles generating AIG without mapping [default = %s]\n", pPars->fPureAig? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles optimizing average rather than maximum level [default = %s]\n", pPars->fDoAverage? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles using cut splitting [default = %s]\n", pPars->fCutGroup? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Mf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Mf_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFARLEDWaekmclgvwh" ) ) != EOF )
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
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
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
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
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'e':
            pPars->fOptEdge ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'c':
            pPars->fGenCnf ^= 1;
            break;
        case 'l':
            pPars->fGenLit ^= 1;
            break;
        case 'g':
            pPars->fPureAig ^= 1;
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

    pNew = Mf_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Lf(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    if ( pPars->fGenCnf )
        Cnf_DataFree( (Cnf_Dat_t*)pAbc->pGia->pData ), pAbc->pGia->pData = NULL;
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &mf [-KCFARLED num] [-akmcgvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : the number of area flow rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-A num   : the number of exact area rounds [default = %d]\n", pPars->nRoundsEla );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n", pPars->nRelaxRatio );
    Abc_Print( -2, "\t-L num   : the fanout limit for coarsening XOR/MUX (num >= 2) [default = %d]\n", pPars->nCoarseLimit );
    Abc_Print( -2, "\t-E num   : the area/edge tradeoff parameter (0 <= num <= 100) [default = %d]\n", pPars->nAreaTuner );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggles edge vs node minimization [default = %s]\n", pPars->fOptEdge? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n", pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles mapping for CNF generation [default = %s]\n", pPars->fGenCnf? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggles mapping for literals [default = %s]\n", pPars->fGenLit? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles generating AIG without mapping [default = %s]\n", pPars->fPureAig? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Of( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Of_ManSetDefaultPars( Jf_Par_t * pPars );
    extern Gia_Man_t * Of_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars );
    char Buffer[200];
    Jf_Par_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew; int c;
    Of_ManSetDefaultPars( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFARLEDNMQekmpgtvwh" ) ) != EOF )
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
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
                Abc_Print( 1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
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
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nDelayLut1 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDelayLut1 < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nDelayLut2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDelayLut2 < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nFastEdges = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFastEdges < 0 )
                goto usage;
            break;
        case 'e':
            pPars->fOptEdge ^= 1;
            break;
        case 'k':
            pPars->fCoarsen ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'g':
            pPars->fPureAig ^= 1;
            break;
        case 't':
            pPars->fDoAverage ^= 1;
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
    if ( Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has mapping. Run \"&st\".\n" );
        return 1;
    }

    pNew = Of_ManPerformMapping( pAbc->pGia, pPars );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Of(): Mapping into LUTs has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 )
        sprintf(Buffer, "best possible" );
    else
        sprintf(Buffer, "%d", pPars->DelayTarget );
    Abc_Print( -2, "usage: &of [-KCFARLEDNMQ num] [-kmpgtvwh]\n" );
    Abc_Print( -2, "\t           performs technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", pPars->nLutSizeMax, pPars->nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", pPars->nCutNumMax, pPars->nCutNum );
    Abc_Print( -2, "\t-F num   : the number of area flow rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-A num   : the number of exact area rounds [default = %d]\n", pPars->nRoundsEla );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n", pPars->nRelaxRatio );
    Abc_Print( -2, "\t-L num   : the fanout limit for coarsening XOR/MUX (num >= 2) [default = %d]\n", pPars->nCoarseLimit );
    Abc_Print( -2, "\t-E num   : the area/edge tradeoff parameter (0 <= num <= 100) [default = %d]\n", pPars->nAreaTuner );
    Abc_Print( -2, "\t-D num   : sets the delay constraint for the mapping [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-N num   : delay of the first LUT [default = %d]\n", pPars->nDelayLut1 );
    Abc_Print( -2, "\t-M num   : delay of the second LUT [default = %d]\n", pPars->nDelayLut2 );
    Abc_Print( -2, "\t-Q num   : the number of fast non-routable edges [default = %d]\n", pPars->nFastEdges );
    Abc_Print( -2, "\t-e       : toggles edge vs node minimization [default = %s]\n", pPars->fOptEdge? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n", pPars->fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggles power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles generating AIG without mapping [default = %s]\n", pPars->fPureAig? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles optimizing average rather than maximum level [default = %s]\n", pPars->fDoAverage? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles very verbose output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Pack( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManLutPacking( Gia_Man_t * p, int nBlock, int DelayRoute, int DelayDir, int fVerbose );
    int c, nBlock = 2, DelayRoute = 10, DelayDir = 2, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NRDvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nBlock = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBlock < 2 )
            {
                Abc_Print( -1, "LUT block size (%d) should be more than 1.\n", nBlock );
                goto usage;
            }
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            DelayRoute = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayRoute <= 0 )
            {
                Abc_Print( -1, "Rounting delay (%d) should be more than 0.\n", DelayRoute);
                goto usage;
            }
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            DelayDir = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayDir <= 0 )
            {
                Abc_Print( -1, "Direct delay (%d) should be more than 0.\n", DelayRoute);
                goto usage;
            }
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
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has no mapping. Run \"&if\".\n" );
        return 1;
    }
    if ( Gia_ManLutSizeMax(pAbc->pGia) > 6 )
        Abc_Print( 0, "Current AIG has mapping into %d-LUTs.\n", Gia_ManLutSizeMax(pAbc->pGia) );
    else
        Gia_ManLutPacking( pAbc->pGia, nBlock, DelayRoute, DelayDir, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &pack [-NRD num] [-vh]\n" );
    Abc_Print( -2, "\t           performs packing for the LUT mapped network\n" );
    Abc_Print( -2, "\t-N num   : the number of LUTs in the block [default = %d]\n", nBlock );
    Abc_Print( -2, "\t-R num   : the routable delay of a LUT [default = %d]\n", DelayRoute );
    Abc_Print( -2, "\t-D num   : the direct (non-routable) delay of a LUT [default = %d]\n", DelayDir );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Edge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Edg_ManAssignEdgeNew( Gia_Man_t * p, int nEdges, int fVerbose );
    extern void Seg_ManComputeDelay( Gia_Man_t * pGia, int Delay, int nFanouts, int fTwo, int fVerbose );
    extern void Sle_ManExplore( Gia_Man_t * pGia, int nBTLimit, int DelayInit, int fDynamic, int fTwoEdges, int fVerbose );

    int c, nBTLimit = 0, DelayMax = 0, nFanouts = 0, nEdges = 1, fReverse = 0, fUsePack = 0, fUseOld = 0, fMapping = 0, fDynamic = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CDFErpomdvh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'C':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nBTLimit = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                break;
            case 'D':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                DelayMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                break;
            case 'F':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nFanouts = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                break;
            case 'E':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-E\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nEdges = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nEdges != 1 && nEdges != 2 )
                {
                    Abc_Print( -1, "Edge limit (%d) should be 1 or 2.\n", nEdges );
                    goto usage;
                }
                break;
            case 'r':
                fReverse ^= 1;
                break;
            case 'p':
                fUsePack ^= 1;
                break;
            case 'o':
                fUseOld ^= 1;
                break;
            case 'm':
                fMapping ^= 1;
                break;
            case 'd':
                fDynamic ^= 1;
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
    if ( fMapping )
    {
        Sle_ManExplore( pAbc->pGia, nBTLimit, DelayMax, fDynamic, nEdges==2, fVerbose );
        return 0;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has no mapping. Run \"&if\".\n" );
        return 1;
    }
    if ( Gia_ManLutSizeMax(pAbc->pGia) > 6 )
    {
        Abc_Print( 0, "Current AIG has mapping into %d-LUTs.\n", Gia_ManLutSizeMax(pAbc->pGia) );
        return 0;
    }
    if ( fUsePack )
    {
        if ( pAbc->pGia->vPacking == NULL )
        {
            Abc_Print( -1, "Packing information is not present.\n" );
            return 0;
        }
        Gia_ManConvertPackingToEdges( pAbc->pGia );
        return 0;
    }
    if ( !fUseOld )
    {
        //Edg_ManAssignEdgeNew( pAbc->pGia, nEdges, fVerbose );
        Seg_ManComputeDelay( pAbc->pGia, DelayMax, nFanouts, nEdges==2, fVerbose );
        return 0;
    }
    if ( pAbc->pGia->pManTime && fReverse )
    {
        Abc_Print( 0, "Reverse computation does not work when boxes are present.\n" );
        return 0;
    }
    if ( fReverse )
        DelayMax = Gia_ManComputeEdgeDelay2( pAbc->pGia );
    else
        DelayMax = Gia_ManComputeEdgeDelay( pAbc->pGia, nEdges == 2 );
    //printf( "The number of edges = %d.  Delay = %d.\n", Gia_ManEvalEdgeCount(pAbc->pGia), DelayMax );
    return 0;

usage:
    Abc_Print( -2, "usage: &edge [-CDFE num] [-rpomdvh]\n" );
    Abc_Print( -2, "\t           find edge assignment of the LUT-mapped network\n" );
    Abc_Print( -2, "\t-C num   : the SAT solver conflict limit (0 = unused) [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-D num   : the upper bound on delay [default = %d]\n", DelayMax );
    Abc_Print( -2, "\t-F num   : skip using edge if fanout higher than this [default = %d]\n", nFanouts );
    Abc_Print( -2, "\t-E num   : the limit on the number of edges (1 <= num <= 2) [default = %d]\n", nEdges );
    Abc_Print( -2, "\t-r       : toggles using reverse order [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggles deriving edges from packing [default = %s]\n", fUsePack? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles using old algorithm [default = %s]\n", fUseOld? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles combining edge assignment with mapping [default = %s]\n", fMapping? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles dynamic addition of clauses [default = %s]\n", fDynamic? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SatLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManLutSat( Gia_Man_t * p, int LutSize, int nNumber, int nImproves, int nBTLimit, int DelayMax, int nEdges, int fDelay, int fReverse, int fVerbose, int fVeryVerbose );
    int c, LutSize = 0, nNumber = 32, nImproves = 0, nBTLimit = 100, DelayMax = 0, nEdges = 0;
    int fDelay = 0, fReverse = 0, fVeryVerbose = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NICDQdrwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nNumber = atoi(argv[globalUtilOptind]);
            if ( nNumber > 128 )
            {
                Abc_Print( -1, "The number of AIG nodes should not exceed 128.\n" );
                goto usage;
            }
            globalUtilOptind++;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nImproves = atoi(argv[globalUtilOptind]);
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
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            DelayMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nEdges = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'd':
            fDelay ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
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
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Current AIG has no mapping. Run \"&if\".\n" );
        return 1;
    }
    LutSize = Gia_ManLutSizeMax(pAbc->pGia);
    if ( LutSize > 6 )
        Abc_Print( 0, "Current AIG is mapped into %d-LUTs (only 6-LUT mapping is currently supported).\n", Gia_ManLutSizeMax(pAbc->pGia) );
    else
        Gia_ManLutSat( pAbc->pGia, LutSize, nNumber, nImproves, nBTLimit, DelayMax, nEdges, fDelay, fReverse, fVerbose, fVeryVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &satlut [-NICDQ num] [-drwvh]\n" );
    Abc_Print( -2, "\t           performs SAT-based remapping of the LUT-mapped network\n" );
    Abc_Print( -2, "\t-N num   : the limit on AIG nodes in the window (num <= 128) [default = %d]\n", nNumber );
    Abc_Print( -2, "\t-I num   : the limit on the number of improved windows [default = %d]\n", nImproves );
    Abc_Print( -2, "\t-C num   : the limit on the number of conflicts [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-D num   : the user-specified required times at the outputs [default = %d]\n", DelayMax );
    Abc_Print( -2, "\t-Q num   : the maximum number of edges [default = %d]\n", nEdges );
    Abc_Print( -2, "\t-d       : toggles delay optimization [default = %s]\n", fDelay? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggles using reverse search [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LNetMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Gia_ManPerformLNetMap( Gia_Man_t * p, int GroupSize, int fUseFixed, int fTryNew, int fVerbose );
    Abc_Ntk_t * pTemp;
    char * pFileName = NULL;
    int c, fTryNew = 1, nIns = 6, nOuts = 2, fUseFixed = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IOfxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nIns = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nOuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'f':
            fUseFixed ^= 1;
            break;
        case 'x':
            fTryNew ^= 1;
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
    if ( argc == globalUtilOptind + 1 )
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
    pTemp = Gia_ManPerformLNetMap( pAbc->pGia, nOuts, fUseFixed, fTryNew, fVerbose );
    Abc_FrameReplaceCurrentNetwork( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &lnetmap [-IO num] [-fxvh] <file>\n" );
    Abc_Print( -2, "\t           performs specialized LUT mapping\n" );
    Abc_Print( -2, "\t-I num   : the input support size [default = %d]\n",         nIns );
    Abc_Print( -2, "\t-O num   : the output group size [default = %d]\n",          nOuts );
    Abc_Print( -2, "\t-f       : toggles using fixed primitives [default = %s]\n", fUseFixed? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles using another computation [default = %s]\n",      fTryNew? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n",         fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<file>   : file name with simulation information\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Unmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManTestStruct( Gia_Man_t * p );
    int c, fConvert = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fConvert ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Struct(): There is no AIG to map.\n" );
        return 1;
    }
    if ( fConvert )
        Cmd_CommandExecute( pAbc, "&put; unmap; &get -m" );    
    else {
        Vec_IntFreeP( &pAbc->pGia->vMapping );
        Vec_IntFreeP( &pAbc->pGia->vPacking );
        Vec_IntFreeP( &pAbc->pGia->vCellMapping );
        Vec_IntFreeP( &pAbc->pGia->vEdge1 );
        Vec_IntFreeP( &pAbc->pGia->vEdge2 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &unmap [-cvh]\n" );
    Abc_Print( -2, "\t           removes mapping from the current network\n" );
    Abc_Print( -2, "\t-c       : toggle converting cell mapping into LUT mapping [default = %s]\n", fConvert? "yes": "no" );
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
int Abc_CommandAbc9Trace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManDelayTraceDump( Gia_Man_t * p, char * pFileName );
    int c;
    int fUseLutLib;
    int fUseCellLib;
    int fVerbose;
    const char * pFileName = NULL;
    // set defaults
    fUseLutLib = 0;
    fUseCellLib = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "F:lcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            pFileName = globalUtilOptarg;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'c':
            fUseCellLib ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Trace(): There is no AIG to map.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Trace(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    if ( fUseLutLib && fUseCellLib )
    {
        Abc_Print( -1, "Abc_CommandAbc9Trace(): Cannot use both LUT library (-l) and cell library (-c) simultaneously.\n" );
        return 1;
    }
    pAbc->pGia->pLutLib = fUseLutLib ? Abc_FrameReadLibLut() : NULL;
    pAbc->pGia->pCellLib = fUseCellLib ? Abc_FrameReadLibCell() : NULL;

    Gia_ManDelayTraceDump( pAbc->pGia, (char *)pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: &trace [-F file] [-lcvh]\n" );
    Abc_Print( -2, "\t           performs delay trace of LUT-mapped network\n" );
    Abc_Print( -2, "\t-F file  : dump the critical path to a file [default = stdout]\n" );
    Abc_Print( -2, "\t-l       : toggle using LUT-library-delay model [default = %s]\n", fUseLutLib? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle using cell-library-delay model [default = %s]\n", fUseCellLib? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
