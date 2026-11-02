/**CFile****************************************************************

  FileName    [abcSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Sequential synthesis.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "aig/saig/saig.h"
#include "opt/cgt/cgt.h"
#include "opt/ret/retInt.h"
#include "opt/fret/fretime.h"
#include "opt/dar/dar.h"
#include "opt/cut/cut.h"
#include "proof/cec/cec.h"
#include "proof/dch/dch.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandAddFlop                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFrames                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDFrames                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewriteSeq            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandScut                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInit                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandZero                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUndc                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneHot                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPipe                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeq                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnseq                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRetime                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRetime                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFlowRetime             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCRetime                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep2              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestSeqSweep           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestScorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLcorr                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqCleanup             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCycle                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDarPhase               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSynch                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandClockGate              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtWin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInsWin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SetRegNum          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Add1Hot            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Frames             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Retime             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Enable             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Synch2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scl                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Lcorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scorr2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scorr3             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scorr4             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sresub             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cycle              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AddFlop            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Init1              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Pipeline           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Unpipeline         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Regio              ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

/**Function*************************************************************

  Synopsis    [Registers sequential synthesis commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitSeq( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Various",      "addflop",       Abc_CommandAddFlop,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "frames",        Abc_CommandFrames,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "dframes",       Abc_CommandDFrames,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irws",          Abc_CommandIRewriteSeq,      1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "scut",          Abc_CommandScut,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "init",          Abc_CommandInit,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "zero",          Abc_CommandZero,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "undc",          Abc_CommandUndc,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "onehot",        Abc_CommandOneHot,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "pipe",          Abc_CommandPipe,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "retime",        Abc_CommandRetime,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "dretime",       Abc_CommandDRetime,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "fretime",       Abc_CommandFlowRetime,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cretime",       Abc_CommandCRetime,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "ssweep",        Abc_CommandSeqSweep,         1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "scorr",         Abc_CommandSeqSweep2,        1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "testssw",       Abc_CommandTestSeqSweep,     0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "testscorr",     Abc_CommandTestScorr,        0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "lcorr",         Abc_CommandLcorr,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "scleanup",      Abc_CommandSeqCleanup,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cycle",         Abc_CommandCycle,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "phase",         Abc_CommandDarPhase,         1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "synch",         Abc_CommandSynch,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "clockgate",     Abc_CommandClockGate,        1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "extwin",        Abc_CommandExtWin,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "inswin",        Abc_CommandInsWin,           1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&setregnum",    Abc_CommandAbc9SetRegNum,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&add1hot",      Abc_CommandAbc9Add1Hot,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&frames",       Abc_CommandAbc9Frames,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&retime",       Abc_CommandAbc9Retime,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&enable",       Abc_CommandAbc9Enable,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&synch2",       Abc_CommandAbc9Synch2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scl",          Abc_CommandAbc9Scl,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lcorr",        Abc_CommandAbc9Lcorr,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scorr",        Abc_CommandAbc9Scorr,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scorr2",       Abc_CommandAbc9Scorr2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scorr3",       Abc_CommandAbc9Scorr3,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scorr4",       Abc_CommandAbc9Scorr4,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sresub",       Abc_CommandAbc9Sresub,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cycle",        Abc_CommandAbc9Cycle,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&addflop",      Abc_CommandAbc9AddFlop,                0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&init1",        Abc_CommandAbc9Init1,                  0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&pipe",         Abc_CommandAbc9Pipeline,               0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&unpipe",       Abc_CommandAbc9Unpipeline,             0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&regio",        Abc_CommandAbc9Regio,                  0 );
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
int Abc_CommandAddFlop( Abc_Frame_t * pAbc, int argc, char ** argv )
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
        Abc_Print( -2, "The current network is not an AIG (run \"strash\").\n");
        return 0;
    }
    // get the new network
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Ntk_t * pNtkRes = Abc_NtkDup( pNtk );
        Abc_NtkAddLatch( pNtkRes, Abc_AigConst1(pNtkRes), ABC_INIT_ONE );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: addflop [-h]\n" );
    Abc_Print( -2, "\t         if the network has no flops, add one dummy flop\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFrames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp, * pNtkRes;
    int nFrames;
    int fInitial;
    int fVerbose;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nFrames  = 5;
    fInitial = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fivh" ) ) != EOF )
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
            if ( nFrames <= 0 )
                goto usage;
            break;
        case 'i':
            fInitial ^= 1;
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

    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes  = Abc_NtkFrames( pNtkTemp, nFrames, fInitial, fVerbose );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes  = Abc_NtkFrames( pNtk, nFrames, fInitial, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Unrolling the network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: frames [-F <num>] [-ivh]\n" );
    Abc_Print( -2, "\t           unrolls the network for a number of time frames\n" );
    Abc_Print( -2, "\t-F <num> : the number of frames to unroll [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i       : toggles initializing the first frame [default = %s]\n", fInitial? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDFrames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp, * pNtkRes;
    int nPrefix;
    int nFrames;
    int fInitial;
    int fVerbose;
    int c;

    extern Abc_Ntk_t * Abc_NtkDarFrames( Abc_Ntk_t * pNtk, int nPrefix, int nFrames, int fInitial, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nPrefix  = 5;
    nFrames  = 5;
    fInitial = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NFivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPrefix <= 0 )
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
            if ( nFrames <= 0 )
                goto usage;
            break;
        case 'i':
            fInitial ^= 1;
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
    if ( nPrefix > nFrames )
    {
        Abc_Print( -1, "Prefix (%d) cannot be more than the number of frames (%d).\n", nPrefix, nFrames );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes  = Abc_NtkDarFrames( pNtkTemp, nPrefix, nFrames, fInitial, fVerbose );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes  = Abc_NtkDarFrames( pNtk, nPrefix, nFrames, fInitial, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Unrolling the network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dframes [-NF <num>] [-ivh]\n" );
    Abc_Print( -2, "\t         unrolls the network with simplification\n" );
    Abc_Print( -2, "\t-N num : the number of frames to use as prefix [default = %d]\n", nPrefix );
    Abc_Print( -2, "\t-F num : the number of frames to unroll [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i     : toggles initializing the first frame [default = %s]\n", fInitial? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandScut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cut_Params_t Params, * pParams = &Params;
    Cut_Man_t * pCutMan;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern Cut_Man_t * Abc_NtkSeqCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );

    // set defaults
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 1000;  // the max number of cuts kept at a node
    pParams->fTruth    = 0;     // compute truth tables
    pParams->fFilter   = 1;     // filter dominated cuts
    pParams->fSeq      = 1;     // compute sequential cuts
    pParams->fVerbose  = 0;     // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMtvh" ) ) != EOF )
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
        case 'v':
            pParams->fVerbose ^= 1;
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
//    if ( !Abc_NtkIsSeq(pNtk) )
//    {
//        Abc_Print( -1, "Sequential cuts can be computed for sequential AIGs (run \"seq\").\n" );
//        return 1;
//    }
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }

    pCutMan = Abc_NtkSeqCuts( pNtk, pParams );
    Cut_ManStop( pCutMan );
    return 0;

usage:
    Abc_Print( -2, "usage: scut [-K num] [-M num] [-tvh]\n" );
    Abc_Print( -2, "\t         computes k-feasible cuts for the sequential AIG\n" );
    Abc_Print( -2, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    Abc_Print( -2, "\t-M num : max number of cuts stored at a node [default = %d]\n",      pParams->nKeepMax );
    Abc_Print( -2, "\t-t     : toggle truth table computation [default = %s]\n",           pParams->fTruth?   "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",      pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIRewriteSeq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewriteSeq( Abc_Ntk_t * pNtk, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 0;
    fUseZeroCost = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeroCost ^= 1;
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

    pNtkRes = Abc_NtkIvyRewriteSeq( pNtk, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: irws [-zvh]\n" );
    Abc_Print( -2, "\t         perform sequential AIG rewriting\n" );
//    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
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
int Abc_CommandInit( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pObj;
    char * pInitStr = NULL;
    int fZeros    = 0;
    int fOnes     = 0;
    int fRandom   = 0;
    int fDontCare = 0;
    int fUseCexCs = 0;
    int fUseCexNs = 0;
    int c, i;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Szordcnh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a file name.\n" );
                goto usage;
            }
            pInitStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'z':
            fZeros ^= 1;
            break;
        case 'o':
            fOnes ^= 1;
            break;
        case 'r':
            fRandom ^= 1;
            break;
        case 'd':
            fDontCare ^= 1;
            break;
        case 'c':
            fUseCexCs ^= 1;
            break;
        case 'n':
            fUseCexNs ^= 1;
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

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The current network is combinational.\n" );
        return 0;
    }

    if ( pInitStr != NULL )
    {
        if ( (int)strlen(pInitStr) != Abc_NtkLatchNum(pNtk) )
        {
            Abc_Print( -1, "The length of init string (%d) differs from the number of flops (%d).\n", strlen(pInitStr), Abc_NtkLatchNum(pNtk) );
            return 1;
        }
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( pInitStr[i] == '0' )
                Abc_LatchSetInit0( pObj );
            else if ( pInitStr[i] == '1' )
                Abc_LatchSetInit1( pObj );
            else
                Abc_LatchSetInitDc( pObj );
        return 0;
    }

    if ( fZeros )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInit0( pObj );
    }
    else if ( fOnes )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInit1( pObj );
    }
    else if ( fRandom )
    {
        srand( time(NULL) );
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( rand() & 1 )
                Abc_LatchSetInit1( pObj );
            else
                Abc_LatchSetInit0( pObj );
    }
    else if ( fDontCare )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInitDc( pObj );
    }
    else if ( fUseCexCs || fUseCexNs )
    {
        extern Vec_Int_t * Saig_ManReturnFailingState( Aig_Man_t * pMan, Abc_Cex_t * p, int fNextOne );
        Aig_Man_t * pMan;
        Vec_Int_t * vFailState;
        if ( fUseCexCs && fUseCexNs )
        {
            Abc_Print( -1, "The two options (-c and -n) are incompatible.\n" );
            return 0;
        }
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "The current network should be an AIG.\n" );
            return 0;
        }
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( -1, "The current CEX is not available.\n" );
            return 0;
        }
        pMan = Abc_NtkToDar( pNtk, 0, 1 );
        vFailState = Saig_ManReturnFailingState( pMan, pAbc->pCex, fUseCexNs );
        //Vec_IntPrint( vFailState );
        Aig_ManStop( pMan );
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Vec_IntEntry( vFailState, i ) )
                Abc_LatchSetInit1( pObj );
            else
                Abc_LatchSetInit0( pObj );
        Vec_IntFree( vFailState );
    }
    else
        Abc_Print( -1, "The initial states remain unchanged.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: init [-zordcnh] [-S <init_string>]\n" );
    Abc_Print( -2, "\t         resets initial states of all latches\n" );
    Abc_Print( -2, "\t-z     : set zeros initial states [default = %s]\n", fZeros? "yes": "no" );
    Abc_Print( -2, "\t-o     : set ones initial states [default = %s]\n", fOnes? "yes": "no" );
    Abc_Print( -2, "\t-d     : set don't-care initial states [default = %s]\n", fDontCare? "yes": "no" );
    Abc_Print( -2, "\t-r     : set random initial states [default = %s]\n", fRandom? "yes": "no" );
    Abc_Print( -2, "\t-c     : set failure current state from the CEX (and run \"zero\") [default = %s]\n", fUseCexCs? "yes": "no" );
    Abc_Print( -2, "\t-n     : set next state after failure from the CEX (and run \"zero\") [default = %s]\n", fUseCexNs? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-S str : (optional) initial state  [default = unused]\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandZero( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
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

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The current network is combinational.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkRestrashZero( pNtk, 0 );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to sequential AIG has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: zero [-h]\n" );
    Abc_Print( -2, "\t        converts latches to have const-0 initial value\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUndc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fUseCex = 0;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fUseCex ^= 1;
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

    if ( fUseCex )
    {
        char * pInit;
        Abc_Cex_t * pTemp;
        int k, nFlopsX = 0;
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( -1, "Current CEX is not available.\n" );
            return 1;
        }
        pInit = Abc_NtkCollectLatchValuesStr( pAbc->pNtkCur );
        // count the number of X-valued flops
        for ( k = 0; k < Abc_NtkLatchNum(pAbc->pNtkCur); k++ )
            nFlopsX += (int)(pInit[k] == 'x');
        // compare this value
        if ( Abc_NtkPiNum(pNtk) + nFlopsX != pAbc->pCex->nPis )
        {
            Abc_Print( -1, "The number of PIs (%d) plus X-valued flops (%d) in the original network does not match the number of PIs in the current CEX (%d).\n",
                Abc_NtkPiNum(pNtk), Abc_NtkLatchNum(pNtk), pAbc->pCex->nPis );
            return 1;
        }
        pAbc->pCex = Abc_CexTransformUndc( pTemp = pAbc->pCex, pInit );
        assert( pAbc->pCex->nPis == Abc_NtkPiNum(pAbc->pNtkCur) );
        assert( pAbc->pCex->nRegs == Abc_NtkLatchNum(pAbc->pNtkCur) );
        Abc_CexFree( pTemp );
        ABC_FREE( pInit );
        return 0;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The current network is combinational.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 0;
    }

    // get the new network
    Abc_NtkConvertDcLatches( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: undc [-ch]\n" );
    Abc_Print( -2, "\t        converts latches with DC init values into free PIs\n" );
    Abc_Print( -2, "\t-c    : toggles transforming CEX after \"logic;undc;st;zero\" [default = %s]\n", fUseCex? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOneHot( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkConvertOnehot( Abc_Ntk_t * pNtk );

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
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The current network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 0;
    }
    // get the new network
    pNtkRes = Abc_NtkConvertOnehot( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to one-hot encoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: onehot [-h]\n" );
    Abc_Print( -2, "\t        converts natural encoding into one-hot encoding\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPipe( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nLatches;
    extern void Abc_NtkLatchPipe( Abc_Ntk_t * pNtk, int nLatches );
    // set defaults
    nLatches = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLatches = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLatches < 0 )
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

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( 0, "Abc_CommandPipe(): Expecting a logic network (run command \"logic\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "Abc_CommandPipe(): Expecting a combinational network.\n" );
        return 0;
    }

    // update the network
    Abc_NtkLatchPipe( pNtk, nLatches );
    return 0;

usage:
    Abc_Print( -2, "usage: pipe [-L num] [-h]\n" );
    Abc_Print( -2, "\t         inserts the given number of latches at each PI for pipelining\n" );
    Abc_Print( -2, "\t-L num : the number of latches to insert [default = %d]\n", nLatches );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

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

    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network has no latches.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Conversion to sequential AIG works only for combinational AIGs (run \"strash\").\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkAigToSeq( pNtk );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to sequential AIG has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: seq [-h]\n" );
    Abc_Print( -2, "\t        converts AIG into sequential AIG\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnseq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fShare;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fShare = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShare ^= 1;
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
//    if ( !Abc_NtkIsSeq(pNtk) )
//    {
//        Abc_Print( -1, "Conversion to combinational AIG works only for sequential AIG (run \"seq\").\n" );
//        return 1;
//    }
    // share the latches on the fanout edges
//    if ( fShare )
//        Seq_NtkShareFanouts(pNtk);

    // get the new network
//    pNtkRes = Abc_NtkSeqToLogicSop( pNtk );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting sequential AIG into an SOP logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: unseq [-sh]\n" );
    Abc_Print( -2, "\t        converts sequential AIG into an SOP logic network\n" );
    Abc_Print( -2, "\t-s    : toggle sharing latches [default = %s]\n", fShare? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMaxIters;
    int fForward;
    int fBackward;
    int fOneStep;
    int fUseOldNames;
    int fVerbose;
    int Mode;
    int nDelayLim;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Mode      =  5;
    nDelayLim =  0;
    fForward  =  0;
    fBackward =  0;
    fOneStep  =  0;
    fUseOldNames = 0;
    fVerbose  =  0;
    nMaxIters = 15;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MDfbsovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Mode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Mode < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDelayLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDelayLim < 0 )
                goto usage;
            break;
        case 'f':
            fForward ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
            break;
        case 's':
            fOneStep ^= 1;
            break;
        case 'o':
            fUseOldNames ^= 1;
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

    if ( fForward && fBackward )
    {
        Abc_Print( -1, "Only one switch \"-f\" or \"-b\" can be selected at a time.\n" );
        return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
//        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( Mode < 0 || Mode > 6 )
    {
        Abc_Print( -1, "The mode (%d) is incorrect. Retiming is not performed.\n", Mode );
        return 0;
    }

    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            Abc_Print( -1, "Retiming with choice nodes is not implemented.\n" );
            return 0;
        }
        // convert the network into an SOP network
        pNtkRes = Abc_NtkToLogic( pNtk );
        // perform the retiming
        Abc_NtkRetime( pNtkRes, Mode, nDelayLim, fForward, fBackward, fOneStep, fUseOldNames, fVerbose );
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }

    // get the network in the SOP form
    if ( !Abc_NtkToSop(pNtk, -1, ABC_INFINITY) )
    {
        Abc_Print( -1, "Converting to SOPs has failed.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "The network is not a logic network. Retiming is not performed.\n" );
        return 0;
    }

    // perform the retiming
    Abc_NtkRetime( pNtk, Mode, nDelayLim, fForward, fBackward, fOneStep, fUseOldNames, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: retime [-MD num] [-fbsovh]\n" );
    Abc_Print( -2, "\t         retimes the current network using one of the algorithms:\n" );
    Abc_Print( -2, "\t             1: most forward retiming\n" );
    Abc_Print( -2, "\t             2: most backward retiming\n" );
    Abc_Print( -2, "\t             3: forward and backward min-area retiming\n" );
    Abc_Print( -2, "\t             4: forward and backward min-delay retiming\n" );
    Abc_Print( -2, "\t             5: mode 3 followed by mode 4\n" );
    Abc_Print( -2, "\t             6: Pan's optimum-delay retiming using binary search\n" );
    Abc_Print( -2, "\t-M num : the retiming algorithm to use [default = %d]\n", Mode );
    Abc_Print( -2, "\t-D num : the minimum delay target (0=unused) [default = %d]\n", nDelayLim );
    Abc_Print( -2, "\t-f     : enables forward-only retiming in modes 3,4,5 [default = %s]\n", fForward? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming in modes 3,4,5 [default = %s]\n", fBackward? "yes": "no" );
    Abc_Print( -2, "\t-s     : enables retiming one step only in mode 4 [default = %s]\n", fOneStep? "yes": "no" );
    Abc_Print( -2, "\t-o     : enables usind old flop naming conventions [default = %s]\n", fUseOldNames? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
//    Abc_Print( -2, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
//    Abc_Print( -2, "\t-f     : toggle forward retiming (for AIGs) [default = %s]\n", fForward? "yes": "no" );
//    Abc_Print( -2, "\t-b     : toggle backward retiming (for AIGs) [default = %s]\n", fBackward? "yes": "no" );
//    Abc_Print( -2, "\t-i     : toggle computation of initial state [default = %s]\n", fInitial? "yes": "no" );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fMinArea;
    int fForwardOnly;
    int fBackwardOnly;
    int fInitial;
    int nStepsMax;
    int fFastAlgo;
    int fVerbose;
    int c, nMaxIters;
    extern Abc_Ntk_t * Abc_NtkDarRetime( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeF( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeMinArea( Abc_Ntk_t * pNtk, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeMostFwd( Abc_Ntk_t * pNtk, int nMaxIters, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMinArea  = 1;
    fForwardOnly = 0;
    fBackwardOnly = 0;
    fInitial = 1;
    nStepsMax = 100000;
    fFastAlgo = 0;
    nMaxIters = 20;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSmfbiavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nStepsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStepsMax < 0 )
                goto usage;
            break;
        case 'm':
            fMinArea ^= 1;
            break;
        case 'f':
            fForwardOnly ^= 1;
            break;
        case 'b':
            fBackwardOnly ^= 1;
            break;
        case 'i':
            fInitial ^= 1;
            break;
        case 'a':
            fFastAlgo ^= 1;
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

    if ( !Abc_NtkLatchNum(pNtk) )
    {
//        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // perform the retiming
    if ( fMinArea )
        pNtkRes = Abc_NtkDarRetimeMinArea( pNtk, nMaxIters, fForwardOnly, fBackwardOnly, fInitial, fVerbose );
    else if ( fFastAlgo )
        pNtkRes = Abc_NtkDarRetime( pNtk, nStepsMax, fVerbose );
    else
//        pNtkRes = Abc_NtkDarRetimeF( pNtk, nStepsMax, fVerbose );
        pNtkRes = Abc_NtkDarRetimeMostFwd( pNtk, nMaxIters, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Retiming has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dretime [-NS num] [-mfbiavh]\n" );
    Abc_Print( -2, "\t         new implementation of min-area (or most-forward) retiming\n" );
    Abc_Print( -2, "\t-m     : toggle min-area retiming and most-forward retiming [default = %s]\n", fMinArea? "min-area": "most-fwd" );
    Abc_Print( -2, "\t-f     : enables forward-only retiming [default = %s]\n", fForwardOnly? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming [default = %s]\n", fBackwardOnly? "yes": "no" );
    Abc_Print( -2, "\t-i     : enables init state computation [default = %s]\n", fInitial? "yes": "no" );
    Abc_Print( -2, "\t-N num : the max number of one-frame iterations to perform [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-S num : the max number of forward retiming steps to perform [default = %d]\n", nStepsMax );
    Abc_Print( -2, "\t-a     : enables a fast most-forward algorithm [default = %s]\n", fFastAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFlowRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMaxIters;
    int fForward;
    int fBackward;
    int fVerbose;
    int fComputeInit, fGuaranteeInit, fBlockConst;
    int fFastButConservative;
    int maxDelay;

    extern Abc_Ntk_t* Abc_FlowRetime_MinReg( Abc_Ntk_t * pNtk, int fVerbose,
                                             int fComputeInit, int fGuaranteeInit, int fBlockConst,
                                             int fForward, int fBackward, int nMaxIters,
                                             int maxDelay, int fFastButConservative);

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fForward  =  0;
    fFastButConservative = 0;
    fBackward =  0;
    fComputeInit =  1;
    fGuaranteeInit =  0;
    fVerbose  =  0;
    fBlockConst  =  0;
    nMaxIters = 999;
    maxDelay  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MDfcgbkivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            maxDelay = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( maxDelay < 0 )
                goto usage;
           break;
        case 'f':
            fForward ^= 1;
            break;
        case 'c':
            fFastButConservative ^= 1;
            break;
        case 'i':
            fComputeInit ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
            break;
        case 'g':
            fGuaranteeInit ^= 1;
            break;
        case 'k':
            fBlockConst ^= 1;
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

    if ( fForward && fBackward )
    {
        Abc_Print( -1, "Only one switch \"-f\" or \"-b\" can be selected at a time.\n" );
        return 1;
    }

    if ( fGuaranteeInit && !fComputeInit )
    {
      Abc_Print( -1, "Initial state guarantee (-g) requires initial state computation (-i).\n" );
      return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( Abc_NtkGetChoiceNum(pNtk) )
      {
        Abc_Print( -1, "Retiming with choice nodes is not implemented.\n" );
        return 0;
      }

    // perform the retiming
    pNtkRes = Abc_FlowRetime_MinReg( pNtk, fVerbose, fComputeInit,
                                     fGuaranteeInit, fBlockConst,
                                     fForward, fBackward,
                                     nMaxIters, maxDelay, fFastButConservative );

    if (pNtkRes != pNtk)
      Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );

    return 0;

usage:
    Abc_Print( -2, "usage: fretime [-M num] [-D num] [-fbvih]\n" );
    Abc_Print( -2, "\t         retimes the current network using flow-based algorithm\n" );
    Abc_Print( -2, "\t-M num : the maximum number of iterations [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-D num : the maximum delay [default = none]\n" );
    Abc_Print( -2, "\t-i     : enables init state computation [default = %s]\n", fComputeInit? "yes": "no" );
    Abc_Print( -2, "\t-k     : blocks retiming over const nodes [default = %s]\n", fBlockConst? "yes": "no" );
    Abc_Print( -2, "\t-g     : guarantees init state computation [default = %s]\n", fGuaranteeInit? "yes": "no" );
    Abc_Print( -2, "\t-c     : very fast (but conserv.) delay constraints [default = %s]\n", fFastButConservative? "yes": "no" );
    Abc_Print( -2, "\t-f     : enables forward-only retiming  [default = %s]\n", fForward? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming [default = %s]\n", fBackward? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkCRetime( Abc_Ntk_t * pNtk, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fVerbose    = 0;
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
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for logic networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkCRetime( pNtk, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cretime [-vh]\n" );
    Abc_Print( -2, "\t         performs most-forward retiming with equiv classes\n" );
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
int Abc_CommandSeqSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Fra_Ssw_t Pars, * pPars = &Pars;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, Fra_Ssw_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    pPars->nPartSize  = 0;
    pPars->nOverSize  = 0;
    pPars->nFramesP   = 0;
    pPars->nFramesK   = 1;
    pPars->nMaxImps   = 5000;
    pPars->nMaxLevs   = 0;
    pPars->fUseImps   = 0;
    pPars->fRewrite   = 0;
    pPars->fFraiging  = 0;
    pPars->fLatchCorr = 0;
    pPars->fWriteImps = 0;
    pPars->fUse1Hot   = 0;
    pPars->fVerbose   = 0;
    pPars->TimeLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQNFILirfletvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesP < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxImps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxImps <= 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 )
                goto usage;
            break;
        case 'i':
            pPars->fUseImps ^= 1;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 'f':
            pPars->fFraiging ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'e':
            pPars->fWriteImps ^= 1;
            break;
        case 't':
            pPars->fUse1Hot ^= 1;
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

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    if ( pPars->nFramesK > 1 && pPars->fUse1Hot )
    {
        Abc_Print( -1, "Currrently can only use one-hotness for simple induction (K=1).\n" );
        return 0;
    }

    if ( pPars->nFramesP && pPars->fUse1Hot )
    {
        Abc_Print( -1, "Currrently can only use one-hotness without prefix.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDarSeqSweep( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: ssweep [-PQNFL <num>] [-lrfetvh]\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-N num : number of time frames to use as the prefix [default = %d]\n", pPars->nFramesP );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
//    Abc_Print( -2, "\t-I num : max number of implications to consider [default = %d]\n", pPars->nMaxImps );
//    Abc_Print( -2, "\t-i     : toggle using implications [default = %s]\n", pPars->fUseImps? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle latch correspondence only [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle AIG rewriting [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle fraiging (combinational SAT sweeping) [default = %s]\n", pPars->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle writing implications as assertions [default = %s]\n", pPars->fWriteImps? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using one-hotness conditions [default = %s]\n", pPars->fUse1Hot? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqSweep2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Ssw_Pars_t Pars, * pPars = &Pars;
    int c, nConstrs = 0;
    extern Abc_Ntk_t * Abc_NtkDarSeqSweep2( Abc_Ntk_t * pNtk, Ssw_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Ssw_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQFCLSIVMNXRBcmplkodsefqvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 )
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
            if ( pPars->nBTLimit <= 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesAddSim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesAddSim < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nItersStop = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nItersStop < 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax2 < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRecycleCalls2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRecycleCalls2 < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nConstrs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConstrs < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLimitMax < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSkip = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSkip < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSkipLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSkipLimit < 0 )
                goto usage;
            break;
        case 'c':
            pPars->fConstrs ^= 1;
            break;
        case 'm':
            pPars->fMergeFull ^= 1;
            break;
        case 'p':
            pPars->fPolarFlip ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'k':
            pPars->fConstCorr ^= 1;
            break;
        case 'o':
            pPars->fOutputCorr ^= 1;
            break;
//        case 'f':
//            pPars->fSemiFormal ^= 1;
//            break;
        case 'd':
            pPars->fDynamic ^= 1;
            break;
        case 's':
            pPars->fLocalSim ^= 1;
            break;
        case 'e':
            pPars->fEquivDump ^= 1;
            break;
        case 'f':
            pPars->fEquivDump2 ^= 1;
            break;
        case 'q':
            pPars->fStopWhenGone ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fFlopVerbose ^= 1;
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

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( 0, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( 0, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    if ( Abc_NtkPiNum(pNtk) == 0 )
    {
        Abc_Print( 0, "This command works only for designs with primary inputs.\n" );
        return 0;
    }

    // if constraints are to be used, network should have no constraints
    if ( nConstrs > 0 )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
        {
            Abc_Print( -1, "The network already has %d constraints.\n", Abc_NtkConstrNum(pNtk) );
            return 0;
        }
        else
        {
            Abc_Print( 0, "Setting the number of constraints to be %d.\n", nConstrs );
            pNtk->nConstrs = nConstrs;
        }
    }

    if ( pPars->fConstrs )
    {
        if ( Abc_NtkConstrNum(pNtk) == Abc_NtkPoNum(pNtk) )
        {
            Abc_Print( 0, "Command cannot be applied because the network has only constraint outputs (no primary outputs).\n" );
            return 0;
        }
        if ( Abc_NtkConstrNum(pNtk) > 0 )
            Abc_Print( 0, "Performing scorr with %d constraints.\n", Abc_NtkConstrNum(pNtk) );
        else
        {
            Abc_Print( 0, "Performing constraint-based scorr without constraints.\n" );
            pPars->fConstrs = 0;
        }
    }
    if ( pPars->fEquivDump && pPars->fEquivDump2 )
    {
        Abc_Print( 0, "Command line switches \'-e\' and \'-f\' cannot be used at the same time.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDarSeqSweep2( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: scorr [-PQFCLSIVMNXRB <num>] [-cmplkodsefqvwh]\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-C num : max number of conflicts at a node (0=inifinite) [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
    Abc_Print( -2, "\t-N num : number of last POs treated as constraints (0=none) [default = %d]\n", pPars->fConstrs );
    Abc_Print( -2, "\t-S num : additional simulation frames for c-examples (0=none) [default = %d]\n", pPars->nFramesAddSim );
    Abc_Print( -2, "\t-I num : iteration number to stop and output SR-model (-1=none) [default = %d]\n", pPars->nItersStop );
    Abc_Print( -2, "\t-V num : min var num needed to recycle the SAT solver [default = %d]\n", pPars->nSatVarMax2 );
    Abc_Print( -2, "\t-M num : min call num needed to recycle the SAT solver [default = %d]\n", pPars->nRecycleCalls2 );
    Abc_Print( -2, "\t-N num : set last <num> POs to be constraints (use with -c) [default = %d]\n", nConstrs );
    Abc_Print( -2, "\t-X num : the number of iterations of little or no improvement [default = %d]\n", pPars->nLimitMax );
    Abc_Print( -2, "\t-R num : the number used to skip some constraints [default = %d]\n", pPars->nSkip );
    Abc_Print( -2, "\t-B num : the limit on the size of constraints to skip [default = %d]\n", pPars->nSkipLimit );
    Abc_Print( -2, "\t-c     : toggle using explicit constraints [default = %s]\n", pPars->fConstrs? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle full merge if constraints are present [default = %s]\n", pPars->fMergeFull? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle aligning polarity of SAT variables [default = %s]\n", pPars->fPolarFlip? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle doing latch correspondence [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle doing constant correspondence [default = %s]\n", pPars->fConstCorr? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle doing \'PO correspondence\' [default = %s]\n", pPars->fOutputCorr? "yes": "no" );
//    Abc_Print( -2, "\t-f     : toggle filtering using iterative BMC [default = %s]\n", pPars->fSemiFormal? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dynamic addition of constraints [default = %s]\n", pPars->fDynamic? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle local simulation in the cone of influence [default = %s]\n", pPars->fLocalSim? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle dumping disproved internal equivalences [default = %s]\n", pPars->fEquivDump? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle dumping proved internal equivalences [default = %s]\n", pPars->fEquivDump2? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle quitting when PO is not a constant candidate [default = %s]\n", pPars->fStopWhenGone? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printout of flop equivalences [default = %s]\n", pPars->fFlopVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestSeqSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName;
    Fra_Ssw_t Pars, * pPars = &Pars;
    int c;
//    extern Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, Fra_Ssw_t * pPars );
    extern int Fra_FraigInductionTest( char * pFileName, Fra_Ssw_t * pParams );

    // set defaults
    pPars->nPartSize  = 0;
    pPars->nOverSize  = 0;
    pPars->nFramesP   = 0;
    pPars->nFramesK   = 1;
    pPars->nMaxImps   = 5000;
    pPars->nMaxLevs   = 0;
    pPars->fUseImps   = 0;
    pPars->fRewrite   = 0;
    pPars->fFraiging  = 0;
    pPars->fLatchCorr = 0;
    pPars->fWriteImps = 0;
    pPars->fUse1Hot   = 0;
    pPars->fVerbose   = 0;
    pPars->TimeLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQNFILirfletvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesP < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxImps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxImps <= 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 )
                goto usage;
            break;
        case 'i':
            pPars->fUseImps ^= 1;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 'f':
            pPars->fFraiging ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'e':
            pPars->fWriteImps ^= 1;
            break;
        case 't':
            pPars->fUse1Hot ^= 1;
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
    // get the input file name
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else
    {
        Abc_Print( -1, "File name should be given on the command line.\n" );
        return 1;
    }
    Fra_FraigInductionTest( pFileName, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: testssw [-PQNFL num] [-lrfetvh] <file>\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t         (outputs a file with a set of pairs of equivalent nodes)\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-N num : number of time frames to use as the prefix [default = %d]\n", pPars->nFramesP );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
//    Abc_Print( -2, "\t-I num : max number of implications to consider [default = %d]\n", pPars->nMaxImps );
//    Abc_Print( -2, "\t-i     : toggle using implications [default = %s]\n", pPars->fUseImps? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle latch correspondence only [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle AIG rewriting [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle fraiging (combinational SAT sweeping) [default = %s]\n", pPars->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle writing implications as assertions [default = %s]\n", pPars->fWriteImps? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using one-hotness conditions [default = %s]\n", pPars->fUse1Hot? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestScorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkTestScorr( char * pFileNameIn, char * pFileNameOut, int nStepsMax, int nBTLimit, int fNewAlgo, int fFlopOnly, int fFfNdOnly, int fVerbose );

    Abc_Ntk_t * pNtkRes;
    int c;
    int nConfMax;
    int nStepsMax;
    int fNewAlgo;
    int fFlopOnly;
    int fFfNdOnly;
    int fVerbose;
    // set defaults
    nConfMax  = 100;
    nStepsMax =  -1;
    fNewAlgo  =   0;
    fFlopOnly =   0;
    fFfNdOnly =   0;
    fVerbose  =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CSnfsvh" ) ) != EOF )
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStepsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStepsMax < 0 )
                goto usage;
            break;
        case 'n':
            fNewAlgo ^= 1;
            break;
        case 'f':
            fFlopOnly ^= 1;
            break;
        case 's':
            fFfNdOnly ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Expecting two files names on the command line.\n" );
        goto usage;
    }
    if ( fFlopOnly && fFfNdOnly )
    {
        Abc_Print( -1, "These two options (-f and -s) are incompatible.\n" );
        goto usage;
    }
    // get the new network
    pNtkRes = Abc_NtkTestScorr( argv[globalUtilOptind], argv[globalUtilOptind+1], nStepsMax, nConfMax, fNewAlgo, fFlopOnly, fFfNdOnly, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: testscorr [-CS num] [-nfsvh] <file_in> <file_out>\n" );
    Abc_Print( -2, "\t             outputs the list of sequential equivalences into a file\n" );
    Abc_Print( -2, "\t             (if <file_in> is in BENCH, init state file should be the same directory)\n" );
    Abc_Print( -2, "\t-C num     : limit on the number of conflicts [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-S num     : limit on refinement iterations (-1=no limit, 0=after BMC, etc) [default = %d]\n", nStepsMax );
    Abc_Print( -2, "\t-n         : toggle between \"scorr\" and \"&scorr\" [default = %s]\n", fNewAlgo? "&scorr": "scorr" );
    Abc_Print( -2, "\t-f         : toggle reporting only flop/flop equivs [default = %s]\n", fFlopOnly? "yes": "no" );
    Abc_Print( -2, "\t-s         : toggle reporting only flop/flop and flop/node equivs [default = %s]\n", fFfNdOnly? "yes": "no" );
    Abc_Print( -2, "\t-v         : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h         : print the command usage\n");
    Abc_Print( -2, "\t<file_in>  : input file with design for sequential equivalence computation\n");
    Abc_Print( -2, "\t<file_out> : output file with the list of pairs of equivalent signals\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLcorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFramesP;
    int nConfMax;
    int nVarsMax;
    int nLimitMax;
    int fNewAlgor;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDarLcorr( Abc_Ntk_t * pNtk, int nFramesP, int nConfMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarLcorrNew( Abc_Ntk_t * pNtk, int nVarsMax, int nConfMax, int nLimitMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);



    // set defaults
    nFramesP   =     0;
    nConfMax   =  1000;
    nVarsMax   =  1000;
    nLimitMax  =     0;
    fNewAlgor  =     1;
    fVerbose   =     0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PCSXnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesP < 0 )
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVarsMax < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            nLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimitMax < 0 )
                goto usage;
            break;
        case 'n':
            fNewAlgor ^= 1;
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

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // get the new network
    if ( fNewAlgor )
        pNtkRes = Abc_NtkDarLcorrNew( pNtk, nVarsMax, nConfMax, nLimitMax, fVerbose );
    else
        pNtkRes = Abc_NtkDarLcorr( pNtk, nFramesP, nConfMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lcorr [-PCSX num] [-nvh]\n" );
    Abc_Print( -2, "\t         computes latch correspondence using 1-step induction\n" );
    Abc_Print( -2, "\t-P num : number of time frames to use as the prefix [default = %d]\n", nFramesP );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", nVarsMax );
    Abc_Print( -2, "\t-X num : the number of iterations of little or no improvement [default = %d]\n", nLimitMax );
    Abc_Print( -2, "\t-n     : toggle using new algorithm [default = %s]\n", fNewAlgor? "yes": "no" );
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
int Abc_CommandSeqCleanup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fLatchConst  =   1;
    int fLatchEqual  =   1;
    int fSaveNames   =   1;
    int fUseMvSweep  =   0;
    int nFramesSymb  =   1;
    int nFramesSatur = 512;
    int fVerbose     =   0;
    int fVeryVerbose =   0;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cenmFSvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fLatchConst ^= 1;
            break;
        case 'e':
            fLatchEqual ^= 1;
            break;
        case 'n':
            fSaveNames ^= 1;
            break;
        case 'm':
            fUseMvSweep ^= 1;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesSymb = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesSymb < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesSatur = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesSatur < 0 )
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarLatchSweep( pNtk, fLatchConst, fLatchEqual, fSaveNames, fUseMvSweep, nFramesSymb, nFramesSatur, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: scleanup [-cenmFSvwh]\n" );
    Abc_Print( -2, "\t         performs sequential cleanup of the current network\n" );
    Abc_Print( -2, "\t         by removing nodes and latches that do not feed into POs\n" );
    Abc_Print( -2, "\t-c     : sweep stuck-at latches detected by ternary simulation [default = %s]\n", fLatchConst? "yes": "no" );
    Abc_Print( -2, "\t-e     : merge equal latches (same data inputs and init states) [default = %s]\n", fLatchEqual? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle preserving latch names [default = %s]\n", fSaveNames? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using hybrid ternary/symbolic simulation [default = %s]\n", fUseMvSweep? "yes": "no" );
    Abc_Print( -2, "\t-F num : the number of first frames simulated symbolically [default = %d]\n", nFramesSymb );
    Abc_Print( -2, "\t-S num : the number of frames when symbolic saturation begins [default = %d]\n", nFramesSatur );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose output [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCycle( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int fUseXval;
    int fVerbose;
    extern void Abc_NtkCycleInitState( Abc_Ntk_t * pNtk, int nFrames, int fUseXval, int fVerbose );
    extern void Abc_NtkCycleInitStateSop( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );
    // set defaults
    nFrames    = 100;
    fUseXval   =   0;
    fVerbose   =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fxvh" ) ) != EOF )
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
        case 'x':
            fUseXval ^= 1;
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

    if ( !Abc_NtkIsStrash(pNtk) && !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks or logic SOP networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( fUseXval && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "X-valued simulation only works for AIGs. Run \"strash\".\n" );
        return 0;
    }
    if ( fUseXval )
        Abc_NtkCycleInitState( pNtk, nFrames, 1, fVerbose );
    else if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkCycleInitState( pNtk, nFrames, 0, fVerbose );
    else
        Abc_NtkCycleInitStateSop( pNtk, nFrames, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: cycle [-F num] [-xvh]\n" );
    Abc_Print( -2, "\t         cycles sequential circuit for the given number of timeframes\n" );
    Abc_Print( -2, "\t         to derive a new initial state (which may be on the envelope)\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-x     : use x-valued primary inputs [default = %s]\n", fUseXval? "yes": "no" );
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
int Abc_CommandDarPhase( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nFrames, nPref;
    int fIgnore;
    int fPrint;
    int fUpdateCex;
    int c, fVerbose;
    extern Abc_Ntk_t * Abc_NtkPhaseAbstract( Abc_Ntk_t * pNtk, int nFrames, int nPref, int fIgnore, int fPrint, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames     = 0;
    nPref       = 0;
    fIgnore     = 0;
    fPrint      = 0;
    fUpdateCex  = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FPipcvh" ) ) != EOF )
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
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPref = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPref < 0 )
                goto usage;
            break;
        case 'i':
            fIgnore ^= 1;
            break;
        case 'p':
            fPrint ^= 1;
            break;
        case 'c':
            fUpdateCex ^= 1;
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
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }
    if ( fUpdateCex )
    {
        Abc_Cex_t * pCexNew;
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( -1, "Counter-example is not available.\n" );
            return 1;
        }
        if ( pAbc->pCex->nPis % Abc_NtkPiNum(pNtk) != 0 )
        {
            Abc_Print( -1, "PI count of the CEX is not a multiple of PI count of the current AIG.\n" );
            return 1;
        }
        pCexNew = Abc_CexTransformPhase( pAbc->pCex, Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk), Abc_NtkLatchNum(pNtk) );
        {
            Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
            Gia_Man_t * pGia = Gia_ManFromAig( pAig );
            int iPo = Gia_ManSetFailedPoCex( pGia, pCexNew );
            Gia_ManStop( pGia );
            Aig_ManStop( pAig );
            if ( iPo == -1 )
            {
                Abc_Print( -1, "The counter-example does not fail any of the outputs of the original AIG.\n" );
                return 1;
            }
        }
        Abc_FrameReplaceCex( pAbc, &pCexNew );
        return 0;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( fPrint )
    {
        Abc_NtkPhaseAbstract( pNtk, 0, nPref, fIgnore, 1, fVerbose );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkPhaseAbstract( pNtk, nFrames, nPref, fIgnore, 0, fVerbose );
    if ( pNtkRes == NULL )
    {
//        Abc_Print( -1, "Phase abstraction has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: phase [-FP <num>] [-ipcvh]\n" );
    Abc_Print( -2, "\t         performs sequential cleanup of the current network\n" );
    Abc_Print( -2, "\t         by removing nodes and latches that do not feed into POs\n" );
    Abc_Print( -2, "\t-F num : the number of frames to abstract [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-P num : the number of prefix frames to skip [default = %d]\n", nPref );
    Abc_Print( -2, "\t-i     : toggle ignoring the initial state [default = %s]\n", fIgnore? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle printing statistics about generators [default = %s]\n", fPrint? "yes": "no" );
    Abc_Print( -2, "\t-c     : update the current CEX derived for a new AIG after \"phase\"\n" );
    Abc_Print( -2, "\t         to match the current AIG (the one before \"phase\") [default = %s]\n", fUpdateCex? "yes": "no" );
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
int Abc_CommandSynch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk1, * pNtk2, * pNtk;
    char ** pArgvNew;
    int nArgcNew;
    int fDelete1, fDelete2;
    int c;
    int nWords;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarSynch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nWords, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarSynchOne( Abc_Ntk_t * pNtk, int nWords, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nWords   =  32;
    fVerbose =   1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Wvh" ) ) != EOF )
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
            if ( nWords <= 0 )
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
    if ( nArgcNew == 0 )
    {
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Empty network.\n" );
            return 1;
        }
        pNtkRes = Abc_NtkDarSynchOne( pNtk, nWords, fVerbose );
    }
    else
    {
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches..\n" );
            return 0;
        }

        // modify the current network
        pNtkRes = Abc_NtkDarSynch( pNtk1, pNtk2, nWords, fVerbose );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Synchronization has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: synch [-W <num>] [-vh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         derives and applies synchronization sequence\n" );
    Abc_Print( -2, "\t-W num : the number of simulation words [default = %d]\n", nWords );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first design\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second design\n\n");
    Abc_Print( -2, "\t         If no designs are given on the command line,\n" );
    Abc_Print( -2, "\t         assumes the current network has no initial state,\n" );
    Abc_Print( -2, "\t         derives synchronization sequence and applies it.\n\n" );
    Abc_Print( -2, "\t         If two designs are given on the command line\n" );
    Abc_Print( -2, "\t         assumes both of them have no initial state,\n" );
    Abc_Print( -2, "\t         derives sequences for both designs, synchorinizes\n" );
    Abc_Print( -2, "\t         them, and creates SEC miter comparing two designs.\n\n" );
    Abc_Print( -2, "\t         If only one design is given on the command line,\n" );
    Abc_Print( -2, "\t         considers the second design to be the current network,\n" );
    Abc_Print( -2, "\t         and derives SEC miter for them, as described above.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandClockGate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cgt_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk, * pNtkCare;
    int c;

    extern Abc_Ntk_t * Abc_NtkDarClockGate( Abc_Ntk_t * pNtk, Abc_Ntk_t * pCare, Cgt_Par_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Cgt_SetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LNDCVKavwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLevelMax <= 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCandMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCandMax <= 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOdcMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOdcMax <= 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfMax <= 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVarsMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVarsMin <= 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFlopsMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlopsMin <= 0 )
                goto usage;
            break;
        case 'a':
            pPars->fAreaOnly ^= 1;
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

    if ( argc == globalUtilOptind + 1 )
    {
        pNtkCare = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1, 0 );
        if ( pNtkCare == NULL )
        {
            Abc_Print( -1, "Reading care network has failed.\n" );
            return 1;
        }
        // modify the current network
        pNtkRes = Abc_NtkDarClockGate( pNtk, pNtkCare, pPars );
        Abc_NtkDelete( pNtkCare );
    }
    else if ( argc == globalUtilOptind )
    {
        pNtkRes = Abc_NtkDarClockGate( pNtk, NULL, pPars );
    }
    else
    {
        Abc_Print( -1, "Wrong number of arguments.\n" );
        return 0;
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Clock gating has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: clockgate [-LNDCVK <num>] [-avwh] <file>\n" );
    Abc_Print( -2, "\t         sequential clock gating with observability don't-cares\n" );
    Abc_Print( -2, "\t-L num : max level number of a clock gate [default = %d]\n", pPars->nLevelMax );
    Abc_Print( -2, "\t-N num : max number of candidates for a flop [default = %d]\n", pPars->nCandMax );
    Abc_Print( -2, "\t-D num : max number of ODC levels to consider [default = %d]\n", pPars->nOdcMax );
    Abc_Print( -2, "\t-C num : max number of conflicts at a node [default = %d]\n", pPars->nConfMax );
    Abc_Print( -2, "\t-V num : min number of vars to recycle SAT solver [default = %d]\n", pPars->nVarsMin );
    Abc_Print( -2, "\t-K num : min number of flops to recycle SAT solver [default = %d]\n", pPars->nFlopsMin );
    Abc_Print( -2, "\t-a     : toggle minimizing area-only [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle even more detailed output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile   : (optional) constraints for primary inputs and register outputs\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExtWin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk;
    int c;
    int nObjId;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarExtWin( Abc_Ntk_t * pNtk, int nObjId, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nObjId   = -1;
    nDist    =  5;
    fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NDvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nObjId = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nObjId <= 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist <= 0 )
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
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind )
    {
        Abc_Print( -1, "Not enough command-line arguments.\n" );
        return 1;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarExtWin( pNtk, nObjId, nDist, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Extracting sequential window has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: extwin [-ND <num>] [-vh]\n" );
    Abc_Print( -2, "\t         extracts sequential window from the AIG\n" );
    Abc_Print( -2, "\t-N num : the ID of the object to use as the center [default = %d]\n", nObjId );
    Abc_Print( -2, "\t-D num : the \"radius\" of the window [default = %d]\n", nDist );
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
int Abc_CommandInsWin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk, * pNtkCare;
    int c;
    int nObjId;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarInsWin( Abc_Ntk_t * pNtk, Abc_Ntk_t * pWnd, int nObjId, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nObjId   = -1;
    nDist    =  5;
    fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NDvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nObjId = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nObjId <= 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist <= 0 )
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
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Not enough command-line arguments.\n" );
        return 1;
    }
    pNtkCare = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1, 0 );
    if ( pNtkCare == NULL )
    {
        Abc_Print( -1, "Reading care network has failed.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtkCare) )
    {
        Abc_Ntk_t * pNtkTemp;
        pNtkCare = Abc_NtkStrash( pNtkTemp = pNtkCare, 0, 1, 0 );
        Abc_NtkDelete( pNtkTemp );
    }
    // modify the current network
    pNtkRes = Abc_NtkDarInsWin( pNtk, pNtkCare, nObjId, nDist, fVerbose );
    Abc_NtkDelete( pNtkCare );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Inserting sequential window has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: inswin [-ND <num>] [-vh] <file>\n" );
    Abc_Print( -2, "\t         inserts sequential window into the AIG\n" );
    Abc_Print( -2, "\t-N num : the ID of the object to use as the center [default = %d]\n", nObjId );
    Abc_Print( -2, "\t-D num : the \"radius\" of the window [default = %d]\n", nDist );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile   : file with the AIG to be inserted\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SetRegNum( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, nRegNum = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nRegNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRegNum < 0 )
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SetRegNum(): There is no AIG.\n" );
        return 1;
    }
    if ( nRegNum >= Gia_ManCiNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9SetRegNum(): The number of registers should be less than the number of CIs.\n" );
        return 1;
    }
    if ( nRegNum >= Gia_ManCoNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9SetRegNum(): The number of registers should be less than the number of COs.\n" );
        return 1;
    }
    pAbc->pGia->nRegs = nRegNum;
    return 0;

usage:
    Abc_Print( -2, "usage: &setregnum [-N num] [-h]\n" );
    Abc_Print( -2, "\t         manually sets the number of registers to combine the last PI/PO pairs\n" );
    Abc_Print( -2, "\t-N num : set the number of registers to be the given number [default = %d]\n", nRegNum );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Add1Hot( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Add1Hot(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManDupOneHot( pAbc->pGia );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &add1hot [-vh]\n" );
    Abc_Print( -2, "\t        adds 1-hotness constraints as additional primary outputs\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Frames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManFrames2( Gia_Man_t * pAig, Gia_ParFra_t * pPars );

    Gia_Man_t * pTemp;
    Gia_ParFra_t Pars, * pPars = &Pars;
    int c;
    int nCofFanLit = 0;
    int fNewAlgo = 0;
    int fInitSpecial = 0;
    Gia_ManFraSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FLsoibavh" ) ) != EOF )
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nCofFanLit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCofFanLit < 0 )
                goto usage;
            break;
        case 's':
            pPars->fDisableSt ^= 1;
            break;
        case 'o':
            pPars->fOrPos ^= 1;
            break;
        case 'i':
            pPars->fInit ^= 1;
            break;
        case 'b':
            fInitSpecial ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Frames(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( fInitSpecial )
        pTemp = Gia_ManFramesInitSpecial( pAbc->pGia, pPars->nFrames, pPars->fVerbose );
    else if ( nCofFanLit )
        pTemp = Gia_ManUnrollAndCofactor( pAbc->pGia, pPars->nFrames, nCofFanLit, pPars->fVerbose );
    else if ( fNewAlgo )
        pTemp = Gia_ManFrames2( pAbc->pGia, pPars );
    else
        pTemp = Gia_ManFrames( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &frames [-FL <num>] [-soibavh]\n" );
    Abc_Print( -2, "\t         unrolls the design for several timeframes\n" );
    Abc_Print( -2, "\t-F num : the number of frames to unroll [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-L num : the limit on fanout count of resets/enables to cofactor [default = %d]\n", nCofFanLit );
    Abc_Print( -2, "\t-s     : toggle disabling structural hashing [default = %s]\n", pPars->fDisableSt? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle ORing corresponding POs [default = %s]\n", pPars->fOrPos? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle initializing registers [default = %s]\n", pPars->fInit? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle computing special AIG for BMC [default = %s]\n", fInitSpecial? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using new algorithm [default = %s]\n", fNewAlgo? "yes": "no" );
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
int Abc_CommandAbc9Retime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int nMaxIters = 100;
    int fVerbose  =   0;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Retime(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Gia_ManRetimeForward( pAbc->pGia, nMaxIters, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &retime [-N <num>] [-vh]\n" );
    Abc_Print( -2, "\t         performs most-forward retiming\n" );
    Abc_Print( -2, "\t-N num : the number of incremental iterations [default = %d]\n", nMaxIters );
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
int Abc_CommandAbc9Enable( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fRemove  = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fRemove ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Enable(): There is no AIG.\n" );
        return 1;
    }
    if ( fRemove )
        pTemp = Gia_ManRemoveEnables( pAbc->pGia );
    else
        pTemp = Gia_ManDupSelf( pAbc->pGia );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &enable [-rvh]\n" );
    Abc_Print( -2, "\t         adds or removes flop enable signals\n" );
    Abc_Print( -2, "\t-r     : toggle adding vs. removing enables [default = %s]\n", fRemove? "remove": "add" );
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
int Abc_CommandAbc9Synch2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManAigSynch2( Gia_Man_t * p, void * pPars, int nLutSize, int nRelaxRatio );
    Gia_Man_t * pTemp;
    Dch_Pars_t Pars, * pPars = &Pars;
    int c, nLutSize = 6;
    int nRelaxRatio = 20;
    // set defaults
    Dch_ManSetDefaultParams( pPars );
    pPars->nBTLimit = 100;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCSKRfrvh" ) ) != EOF )
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
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a char string.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-R\" should be followed by a floating point number.\n" );
                return 0;
            }
            nRelaxRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRelaxRatio < 0 )
                goto usage;
            break;
        case 'f':
            pPars->fLightSynth ^= 1;
            break;
        case 'r':
            pPars->fSkipRedSupp ^= 1;
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
    pTemp = Gia_ManAigSynch2( pAbc->pGia, pPars, nLutSize, nRelaxRatio );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &synch2 [-WCSKR num] [-frvh]\n" );
    Abc_Print( -2, "\t         computes structural choices using a new approach\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-K num : the target LUT size for downstream mapping [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-R num : the delay relaxation ratio (num >= 0) [default = %d]\n",   nRelaxRatio );
    Abc_Print( -2, "\t-f     : toggle using lighter logic synthesis [default = %s]\n", pPars->fLightSynth? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle skipping choices with redundant support [default = %s]\n", pPars->fSkipRedSupp? "yes": "no" );
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
int Abc_CommandAbc9Scl( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fConst = 1;
    int fEquiv = 1;
    int fVerbose = 0;
    int fVerboseFlops = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cevwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fConst ^= 1;
            break;
        case 'e':
            fEquiv ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVerboseFlops ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Scl(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) && Gia_ManRegBoxNum(pAbc->pGia) )
    {
        if ( pAbc->pGia->pAigExtra == NULL )
        {
            printf( "Timing manager is given but there is no GIA of boxes.\n" );
            return 0;
        }
        pTemp = Gia_ManSweepWithBoxes( pAbc->pGia, NULL, NULL, fConst, fEquiv, fVerbose, fVerboseFlops );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Gia_ManSeqStructSweep( pAbc->pGia, fConst, fEquiv, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &scl [-cevwh]\n" );
    Abc_Print( -2, "\t         performs structural sequential cleanup\n" );
    Abc_Print( -2, "\t-c     : toggle removing stuck-at constant registers [default = %s]\n", fConst? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle removing equivalent-driver registers [default = %s]\n", fEquiv? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing verbose info about equivalent flops [default = %s]\n", fVerboseFlops? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Lcorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParCor_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->fLatchCorr = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPXrcvwh" ) ) != EOF )
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
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPrefix < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLimitMax < 0 )
                goto usage;
            break;
        case 'r':
            pPars->fUseRings ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVerboseFlops ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Lcorr(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) && Gia_ManRegBoxNum(pAbc->pGia) )
    {
        if ( pAbc->pGia->pAigExtra == NULL )
        {
            printf( "Timing manager is given but there is no GIA of boxes.\n" );
            return 0;
        }
        pTemp = Gia_ManSweepWithBoxes( pAbc->pGia, NULL, pPars, 0, 0, pPars->fVerbose, pPars->fVerboseFlops );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Cec_ManLSCorrespondence( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &lcorr [-FCPX num] [-rcvwh]\n" );
    Abc_Print( -2, "\t         performs latch correpondence computation\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-P num : the number of timeframes in the prefix [default = %d]\n", pPars->nPrefix );
    Abc_Print( -2, "\t-X num : the number of iterations of little or no improvement [default = %d]\n", pPars->nLimitMax );
    Abc_Print( -2, "\t-r     : toggle using implication rings during refinement [default = %s]\n", pPars->fUseRings? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing verbose info about equivalent flops [default = %s]\n", pPars->fVerboseFlops? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Scorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec_ManScorrCorrespondence( Gia_Man_t * p, Cec_ParCor_t * pPars );
    extern Gia_Man_t * Gia_ManScorrDivideTest( Gia_Man_t * p, Cec_ParCor_t * pPars );
    extern Gia_Man_t * Gia_SignalCorrespondencePart( Gia_Man_t * p, Cec_ParCor_t * pPars );
    Cec_ParCor_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int fPartition = 0;
    int nFlopIncFreq = 0;
    int fUseOld = 0, c;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->nProcs = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCGXPSZpkrecqowvh" ) ) != EOF )
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
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPrefix < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLimitMax < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nProcs < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 0 )
                goto usage;
            break;            
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
                goto usage;
            }
            nFlopIncFreq = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFlopIncFreq < 0 )
                goto usage;
            break;            
        case 'p':
            fPartition ^= 1;
            break;
        case 'k':
            pPars->fConstCorr ^= 1;
            break;
        case 'r':
            pPars->fUseRings ^= 1;
            break;
        case 'e':
            pPars->fMakeChoices ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'q':
            pPars->fStopWhenGone ^= 1;
            break;
        case 'o':
            fUseOld ^= 1;
            break;
        case 'w':
            pPars->fVerboseFlops ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Scorr(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) && Gia_ManRegBoxNum(pAbc->pGia) )
    {
        if ( pAbc->pGia->pAigExtra == NULL )
        {
            printf( "Timing manager is given but there is no GIA of boxes.\n" );
            return 0;
        }
        pTemp = Gia_ManSweepWithBoxes( pAbc->pGia, NULL, pPars, 0, 0, pPars->fVerbose, pPars->fVerboseFlops );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "The network is combinational.\n" );
        return 0;
    }
    if ( nFlopIncFreq )
    {
        extern Gia_Man_t * Gia_ManDupStopsAdd( Gia_Man_t * p, Vec_Int_t * vStops );
        extern Gia_Man_t * Gia_ManDupStopsRem( Gia_Man_t * p, Vec_Int_t * vStops );
        extern Vec_Int_t * Gia_ManFindStopFlops( Gia_Man_t * p, int nFlopIncFreq, int fVerbose );
        Vec_Int_t * vStops = Gia_ManFindStopFlops( pAbc->pGia, nFlopIncFreq, pPars->fVerbose );
        if ( vStops )
        {
            extern void Gia_ManTransferEquivs2( Gia_Man_t * p, Gia_Man_t * pNew );
            Gia_Man_t * pUsed = Gia_ManDupStopsAdd( pAbc->pGia, vStops );
            if ( pPars->nPartSize > 0 )
                pTemp = Gia_SignalCorrespondencePart( pUsed, pPars );
            else if ( fUseOld )
                pTemp = Cec_ManScorrCorrespondence( pUsed, pPars );
            else if ( fPartition )
                pTemp = Gia_ManScorrDivideTest( pUsed, pPars );
            else
                pTemp = Cec_ManLSCorrespondence( pUsed, pPars );
            Gia_ManTransferEquivs2( pUsed, pAbc->pGia );
            Gia_ManStop( pUsed );
            pTemp = Gia_ManDupStopsRem( pUsed = pTemp, vStops );
            Gia_ManStop( pUsed );
            Abc_FrameUpdateGia( pAbc, pTemp );
            Vec_IntFree( vStops );
            return 0;
        }
    }
    if ( pPars->nPartSize > 0 )
        pTemp = Gia_SignalCorrespondencePart( pAbc->pGia, pPars );
    else if ( fUseOld )
        pTemp = Cec_ManScorrCorrespondence( pAbc->pGia, pPars );
    else if ( fPartition )
        pTemp = Gia_ManScorrDivideTest( pAbc->pGia, pPars );
    else
        pTemp = Cec_ManLSCorrespondence( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &scorr [-FCGXPSZ num] [-pkrecqowvh]\n" );
    Abc_Print( -2, "\t         performs signal correpondence computation\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-G num : the number of timeframes in the prefix [default = %d]\n", pPars->nPrefix );
    Abc_Print( -2, "\t-X num : the number of iterations of little or no improvement [default = %d]\n", pPars->nLimitMax );
    Abc_Print( -2, "\t-P num : the number of concurrent processes [default = %d]\n", pPars->nProcs );
    Abc_Print( -2, "\t-S num : the number of flops in one partition [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Z num : the average flop include frequency [default = %d]\n", nFlopIncFreq );
    Abc_Print( -2, "\t-p     : toggle using partitioning for the input AIG [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle using constant correspondence [default = %s]\n", pPars->fConstCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using implication rings during refinement [default = %s]\n", pPars->fUseRings? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle using equivalences as choices [default = %s]\n", pPars->fMakeChoices? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle quitting when PO is not a constant candidate [default = %s]\n", pPars->fStopWhenGone? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle calling old engine [default = %s]\n", fUseOld? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing verbose info about equivalent flops [default = %s]\n", pPars->fVerboseFlops? "yes": "no" );
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
int Abc_CommandAbc9Scorr2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec_ManScorrCorrespondence( Gia_Man_t * p, Cec_ParCor_t * pPars );
    extern Gia_Man_t * Cec_ManLSCorrespondence2( Gia_Man_t * p, Cec_ParCor_t * pPars );
    extern Gia_Man_t * Gia_ManScorrDivideTest( Gia_Man_t * p, Cec_ParCor_t * pPars );
    extern Gia_Man_t * Gia_SignalCorrespondencePart( Gia_Man_t * p, Cec_ParCor_t * pPars );
    Cec_ParCor_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int fPartition = 0;
    int fUseOld = 0, c;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->nProcs           = 1;
    pPars->fIncremental     = 1;
    pPars->fDynSrm          = 1;
    pPars->fIncrSim         = 1;
    pPars->fSkipFailResim   = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCGXPSKYDpkrecqiIosvh" ) ) != EOF )
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
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPrefix < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLimitMax < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nProcs < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 0 )
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 'k':
            pPars->fConstCorr ^= 1;
            break;
        case 'r':
            pPars->fUseRings ^= 1;
            break;
        case 'e':
            pPars->fMakeChoices ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'q':
            pPars->fStopWhenGone ^= 1;
            break;
        case 'i':
            pPars->fIncremental ^= 1;
            break;
        case 'D':
            pPars->fDynSrm ^= 1;
            break;
        case 'I':
            pPars->fIncrSim ^= 1;
            break;
        case 's':
            pPars->fSkipFailResim ^= 1;
            break;
        case 'Y':
            pPars->fBmcTasAdaptive ^= 1;
            break;
        case 'K':
            pPars->fKissatCert ^= 1;
            break;
        case 'o':
            fUseOld ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pPars->fDynSrm && !pPars->fIncremental )
    {
        Abc_Print( -1, "The dynamic SRM manager (-D) requires -i.\n" );
        return 1;
    }
    if ( pPars->fBmcTasAdaptive && !pPars->fDynSrm )
    {
        Abc_Print( -1, "The adaptive BMC solver policy (-Y) requires -D.\n" );
        return 1;
    }
    if ( pPars->fKissatCert &&
         (fUseOld || fPartition || pPars->nPartSize > 0 ||
          pPars->nPrefix > 0) )
    {
        Abc_Print( -1, "The strict fixed-point oracle (-K) supports the direct engine with -G 0 only.\n" );
        return 1;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&scorr2: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManBoxNum(pAbc->pGia) && Gia_ManRegBoxNum(pAbc->pGia) )
    {
        if ( pAbc->pGia->pAigExtra == NULL )
        {
            printf( "Timing manager is given but there is no GIA of boxes.\n" );
            return 0;
        }
        pTemp = Gia_ManSweepWithBoxes( pAbc->pGia, NULL, pPars, 0, 0, pPars->fVerbose, pPars->fVerboseFlops );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "The network is combinational.\n" );
        return 0;
    }
    if ( pPars->nPartSize > 0 )
        pTemp = Gia_SignalCorrespondencePart( pAbc->pGia, pPars );
    else if ( fUseOld )
        pTemp = Cec_ManScorrCorrespondence( pAbc->pGia, pPars );
    else if ( fPartition )
        pTemp = Gia_ManScorrDivideTest( pAbc->pGia, pPars );
    else
        pTemp = Cec_ManLSCorrespondence2( pAbc->pGia, pPars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &scorr2 [-FCGXPS num] [-pkrecqiDIsYKovh]\n" );
    Abc_Print( -2, "\t         performs signal correpondence computation using the incremental scorr2 engine\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-G num : the number of timeframes in the prefix [default = %d]\n", pPars->nPrefix );
    Abc_Print( -2, "\t-X num : the number of iterations of little or no improvement [default = %d]\n", pPars->nLimitMax );
    Abc_Print( -2, "\t-P num : the number of concurrent processes [default = %d]\n", pPars->nProcs );
    Abc_Print( -2, "\t-S num : the number of flops in one partition [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-p     : toggle using partitioning for the input AIG [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle using constant correspondence [default = %s]\n", pPars->fConstCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using implication rings during refinement [default = %s]\n", pPars->fUseRings? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle using equivalences as choices [default = %s]\n", pPars->fMakeChoices? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle quitting when PO is not a constant candidate [default = %s]\n", pPars->fStopWhenGone? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle incremental TFO-triggered re-proof [default = %s]\n", pPars->fIncremental? "yes": "no" );
    Abc_Print( -2, "\t-D     : toggle persistent dynamic SRM construction [default = %s]\n", pPars->fDynSrm? "yes": "no" );
    Abc_Print( -2, "\t-I     : toggle persistent event-driven resimulation [default = %s]\n", pPars->fIncrSim? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle skipping resimulation without a real CEX [default = %s]\n", pPars->fSkipFailResim? "yes": "no" );
    Abc_Print( -2, "\t-Y     : toggle guarded CBS-first/TAS-rescue BMC policy [default = %s]\n", pPars->fBmcTasAdaptive? "yes": "no" );
    Abc_Print( -2, "\t-K     : toggle strict final fixed-point Kissat audit [default = %s]\n", pPars->fKissatCert? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle calling old engine [default = %s]\n", fUseOld? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t         This command was contributed by Xiran Zhao from University of Chinese Academy of Sciences (UCAS).\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes signal correspondence with lazy speculative updates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Scorr3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec_ManLSCorrespondence3( Gia_Man_t *, Cec_ParCor_t * );
    Cec_ParCor_t Pars;
    Gia_Man_t * pNew;
    int c;
    Cec_ManCorSetDefaultParams( &Pars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "FCkvh")) != EOF )
    {
        switch ( c )
        {
        case 'F':
        case 'C':
        {
            char * pEnd, * pArg;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            pArg = argv[globalUtilOptind++];
            Value = strtol( pArg, &pEnd, 10 );
            if ( pEnd == pArg || *pEnd || Value < (c == 'F') || Value > 1000000 ) goto usage;
            if ( c == 'F' ) Pars.nFrames = (int)Value;
            else Pars.nBTLimit = (int)Value;
            break;
        }
        case 'k': Pars.fKissatCert ^= 1; break;
        case 'v': Pars.fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( !pAbc->pGia ) { Abc_Print(-1,"&scorr3: There is no AIG.\n"); return 1; }
    if ( !Gia_ManRegNum(pAbc->pGia) ) { Abc_Print(0,"The network is combinational.\n"); return 0; }
    if ( Gia_ManRegBoxNum(pAbc->pGia) ) { Abc_Print(-1,"&scorr3: register boxes are not supported.\n"); return 1; }
    pNew = Cec_ManLSCorrespondence3( pAbc->pGia, &Pars );
    if ( !pNew ) return 1;
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &scorr3 [-FC num] [-kvh]\n" );
    Abc_Print( -2, "\t         performs signal correspondence computation\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", Pars.nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case (at least 1) [default = %d]\n", Pars.nFrames );
    Abc_Print( -2, "\t-k     : toggle auditing final base and step obligations with Kissat [default = %s]\n", Pars.fKissatCert? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", Pars.fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes correspondence with selected inductive constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Scorr4( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec_ManLSCorrespondence4( Gia_Man_t *, Cec_ParCor_t *, int, int );
    Cec_ParCor_t Pars;
    Gia_Man_t * pNew;
    int c, nSides = 4, fRewrite = 0;
    Cec_ManCorSetDefaultParams( &Pars );
    // Match the default proof budget of network-level scorr.
    Pars.nBTLimit = 1000;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "FCSrkvh")) != EOF )
    {
        switch ( c )
        {
        case 'F':
        case 'C':
        case 'S':
        {
            char * pEnd, * pArg;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            pArg = argv[globalUtilOptind++];
            Value = strtol( pArg, &pEnd, 10 );
            if ( pEnd == pArg || *pEnd || Value < (c == 'F' ? 1 : c == 'S' ? -1 : 0) || Value > 1000000 ) goto usage;
            if ( c == 'F' ) Pars.nFrames = (int)Value;
            else if ( c == 'C' ) Pars.nBTLimit = (int)Value;
            else nSides = (int)Value;
            break;
        }
        case 'r': fRewrite ^= 1; break;
        case 'k': Pars.fKissatCert ^= 1; break;
        case 'v': Pars.fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( !pAbc->pGia ) { Abc_Print(-1,"&scorr4: There is no AIG.\n"); return 1; }
    if ( !Gia_ManRegNum(pAbc->pGia) ) { Abc_Print(0,"The network is combinational.\n"); return 0; }
    if ( Gia_ManRegBoxNum(pAbc->pGia) ) { Abc_Print(-1,"&scorr4: register boxes are not supported.\n"); return 1; }
    pNew = Cec_ManLSCorrespondence4( pAbc->pGia, &Pars, nSides, fRewrite );
    if ( !pNew ) return 1;
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &scorr4 [-FCS num] [-rkvh]\n" );
    Abc_Print( -2, "\t         performs signal correspondence computation\n" );
    Abc_Print( -2, "\t-C num : max conflicts at a node (0 = unlimited) [default = %d]\n", Pars.nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case (at least 1) [default = %d]\n", Pars.nFrames );
    Abc_Print( -2, "\t-S num : max inductive side constraints per query (0=none, -1=all) [default = %d]\n", nSides );
    Abc_Print( -2, "\t-r     : toggle level-preserving &drw preprocessing [default = %s]\n", fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle Kissat base/step audits and CEC of optional rewriting [default = %s]\n", Pars.fKissatCert? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", Pars.fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs sequential root resubstitution.]

***********************************************************************/
static int Abc_CommandAbc9Sresub( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParTran_t Pars;
    Gia_Man_t * pResult;
    int c, fStrictOnly = 0;

    Cec_ManTranSetRoute3Params( &Pars, 1 );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "fcspvh")) != EOF )
    {
        if ( c == 'f' || c == 'c' )
        {
            char * pEnd;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            errno = 0;
            Value = strtol( argv[globalUtilOptind++], &pEnd, 10 );
            if ( errno || pEnd == argv[globalUtilOptind-1] ||
                 *pEnd || Value < (c == 'f') || Value > INT_MAX - (c == 'f') ) goto usage;
            if ( c == 'f' ) Pars.nFrames = Pars.nWindowFrames = (int)Value;
            else Pars.nBTLimit = Pars.nWindowConflicts = (int)Value;
            continue;
        }
        switch ( c )
        {
        case 's': fStrictOnly = 1; break;
        case 'p': Pars.fProfile ^= 1; break;
        case 'v': Pars.fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( fStrictOnly ) Pars.fUseOdc = 0;
    if ( !pAbc->pGia || Gia_ManBoxNum(pAbc->pGia) || Gia_ManBufNum(pAbc->pGia) ||
         Gia_ManHasChoices(pAbc->pGia) || pAbc->pGia->pMuxes ||
         Gia_ManXorNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&sresub requires a plain GIA without boxes, buffers, or choices.\n" );
        return 1;
    }
    if ( !Gia_ManRegNum(pAbc->pGia) ) return 0;
    pResult = Cec_ManSequentialTransduction( pAbc->pGia, &Pars );
    if ( !pResult ) return 1;
    Abc_FrameUpdateGia( pAbc, pResult );
    return 0;

usage:
    Abc_Print( -2, "usage: &sresub [-f num] [-c num] [-spvh]\n" );
    Abc_Print( -2, "\t-f num : induction depth in Strict and ODC [default = %d]\n", Pars.nFrames );
    Abc_Print( -2, "\t-c num : SAT conflict limit in Strict and ODC [default = %d]\n", Pars.nBTLimit );
    Abc_Print( -2, "\t-s     : run Strict only\n" );
    Abc_Print( -2, "\t-p     : print exact Build reduction\n" );
    Abc_Print( -2, "\t-v     : print detailed discovery/proof diagnostics\n" );
    Abc_Print( -2, "\t-h     : print command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Cycle( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, nFrames = 10, fUseCex = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fcvh" ) ) != EOF )
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
        case 'c':
            fUseCex ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Cycle(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManDupCycled( pAbc->pGia, fUseCex ? pAbc->pCex : NULL, nFrames );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &cycle [-F num] [-cvh]\n" );
    Abc_Print( -2, "\t         cycles sequential circuit for the given number of timeframes\n" );
    Abc_Print( -2, "\t         to derive a new initial state (which may be on the envelope)\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-c     : toggle using PI values from the current CEX [default = %s]\n", fUseCex? "yes": "no" );
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
int Abc_CommandAbc9AddFlop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupAddFlop( Gia_Man_t * p );
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
        Abc_Print( -1, "Abc_CommandAbc9AddFlop(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 ) 
    {
        pTemp = Gia_ManDupAddFlop( pAbc->pGia );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &addflop [-vh]\n" );
    Abc_Print( -2, "\t         if the design has no flops, adds one flop to the design\n" );
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
int Abc_CommandAbc9Init1( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManFlipInit1( Gia_Man_t * p, Vec_Int_t * vInit );
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
    if ( pAbc->pGia == NULL ) {
        Abc_Print( -1, "Abc_CommandAbc9Init1(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )  {
        Abc_Print( -1, "Abc_CommandAbc9Init1(): There is no flops.\n" );
        return 0;
    }
    if ( pAbc->pGia->vRegInits == NULL ) {
        Abc_Print( -1, "Abc_CommandAbc9Init1(): Flop init states are not available.\n" );
        return 0;
    }
    Gia_ManFlipInit1( pAbc->pGia, pAbc->pGia->vRegInits );
    return 0;

usage:
    Abc_Print( -2, "usage: &init1 [-vh]\n" );
    Abc_Print( -2, "\t         complements the inputs/outputs of flops with const-1 initial state\n" );
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
int Abc_CommandAbc9Pipeline( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupPipeline( Gia_Man_t * p, int nLevels, int fVerbose );
    Gia_Man_t * pGiaNew;
    int nLevels = 20;
    int nDelayMax, c, fVerbose = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels <= 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Pipeline(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Pipeline(): This command expects a combinational AIG.\n" );
        return 1;
    }

    pGiaNew = Gia_ManDupPipeline( pAbc->pGia, nLevels, fVerbose );
    if ( pGiaNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Pipeline(): Pipelining has failed.\n" );
        return 1;
    }
    nDelayMax = Gia_ManLevelNum( pGiaNew );
    if ( nDelayMax > nLevels )
    {
        Abc_Print( -1, "Abc_CommandAbc9Pipeline(): Seed pipeline delay (%d) exceeds target D = %d.\n", nDelayMax, nLevels );
        Gia_ManStop( pGiaNew );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pGiaNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &pipe [-D num] [-vh]\n" );
    Abc_Print( -2, "\t         inserts pipeline stages\n" );
    Abc_Print( -2, "\t-D num : max AIG levels between the flops [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Unpipeline( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupUnpipeline( Gia_Man_t * p, int fVerbose );
    Gia_Man_t * pGiaNew;
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
        Abc_Print( -1, "Abc_CommandAbc9Unpipeline(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        if ( fVerbose )
            Abc_Print( 1, "Abc_CommandAbc9Unpipeline(): The current AIG is already combinational.\n" );
        return 0;
    }

    pGiaNew = Gia_ManDupUnpipeline( pAbc->pGia, fVerbose );
    if ( pGiaNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Unpipeline(): Removing pipeline flops has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pGiaNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &unpipe [-vh]\n" );
    Abc_Print( -2, "\t         removes the flops to derive a combinational AIG\n" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Regio( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupRegio( Gia_Man_t * p, int fRegIns, int fRegOuts, int fVerbose );
    Gia_Man_t * pGiaNew;
    int c, fRegIns = 1, fRegOuts = 1, fVerbose = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "iovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fRegIns ^= 1;
            break;
        case 'o':
            fRegOuts ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Regio(): There is no AIG.\n" );
        return 1;
    }
    if ( !fRegIns && !fRegOuts )
    {
        if ( fVerbose )
            Abc_Print( 1, "Abc_CommandAbc9Regio(): No boundary flops are requested.\n" );
        return 0;
    }

    pGiaNew = Gia_ManDupRegio( pAbc->pGia, fRegIns, fRegOuts, fVerbose );
    if ( pGiaNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Regio(): Adding boundary flops has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pGiaNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &regio [-iovh]\n" );
    Abc_Print( -2, "\t         adds PI/PO flops while preserving the current AIG\n" );
    Abc_Print( -2, "\t-i     : toggle adding PI flops [default = %s]\n", fRegIns ? "yes" : "no" );
    Abc_Print( -2, "\t-o     : toggle adding PO flops [default = %s]\n", fRegOuts ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
