/**CFile****************************************************************

  FileName    [abcVerify.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Sequential verification.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "sat/bmc/bmc.h"
#include "proof/int/int.h"
#include "proof/pdr/pdr.h"
#include "proof/pdr2/pdr2.h"
#include "bdd/llb/llb.h"
#include "bdd/bbr/bbr.h"
#include "base/wln/wln.h"
#include "base/sn/snRead.h"
#include "base/sn/snGia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandReach                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQuaReach               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDProve                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbSec                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSimSec                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDSec                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc2                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc3                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmcInter               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIndcut                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInduction              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPdr                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPdr2                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BackReach          ( Abc_Frame_t * pAbc, int argc, char ** argv );
#ifdef ABC_USE_CUDD
static int Abc_CommandAbc9ReachM             ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
#ifdef ABC_USE_CUDD
static int Abc_CommandAbc9ReachP             ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
#ifdef ABC_USE_CUDD
static int Abc_CommandAbc9ReachN             ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
#ifdef ABC_USE_CUDD
static int Abc_CommandAbc9ReachY             ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
static int Abc_CommandAbc9GroupProve         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MultiProve         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SProve             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SProve2            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Bmc                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SBmc               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ChainBmc           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BCore              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ICheck             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Bmci               ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
typedef struct Wlc_BstPar_t_ Wlc_BstPar_t;
typedef struct Wlc_Ntk_t_    Wlc_Ntk_t;
extern Gia_Man_t * Wlc_NtkBitBlast( Wlc_Ntk_t * p, Wlc_BstPar_t * pPars );
extern int Cec_GiaProveTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nTimeOut2, int nTimeOut3, int fUseUif, Wlc_Ntk_t * pWlc, int fVerbose, int fVeryVerbose, int fSilent, char * pReplayFile, char * pUfarArgs );
extern int Cec_GiaReplayReadParams( char * pFileName, int * pnProcs, int * pnTimeOut, int * pnTimeOut2, int * pnTimeOut3, int * pfUseUif );
extern int Cec_GiaReplayTest( Gia_Man_t * p, Wlc_Ntk_t * pWlc, char * pFileName, int fVerbose, int fVeryVerbose, int fSilent );

/**Function*************************************************************

  Synopsis    [Registers sequential verification commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitVerify( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Various",      "reach",         Abc_CommandReach,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "qreach",        Abc_CommandQuaReach,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "dsec",          Abc_CommandDSec,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "dprove",        Abc_CommandDProve,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "absec",         Abc_CommandAbSec,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "simsec",        Abc_CommandSimSec,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc",           Abc_CommandBmc,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc2",          Abc_CommandBmc2,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc3",          Abc_CommandBmc3,             1 );
    Cmd_CommandAdd( pAbc, "Verification", "int",           Abc_CommandBmcInter,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "indcut",        Abc_CommandIndcut,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "ind",           Abc_CommandInduction,        0 );
    Cmd_CommandAdd( pAbc, "Verification", "pdr",           Abc_CommandPdr,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "pdr2",          Abc_CommandPdr2,             0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&back_reach",   Abc_CommandAbc9BackReach,    0 );
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachm",       Abc_CommandAbc9ReachM,       0 );
#endif
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachp",       Abc_CommandAbc9ReachP,       0 );
#endif
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachn",       Abc_CommandAbc9ReachN,       0 );
#endif
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachy",       Abc_CommandAbc9ReachY,       0 );
#endif
    Cmd_CommandAdd( pAbc, "ABC9",         "&gprove",       Abc_CommandAbc9GroupProve,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mprove",       Abc_CommandAbc9MultiProve,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sprove",       Abc_CommandAbc9SProve,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sprove2",      Abc_CommandAbc9SProve2,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bmc",          Abc_CommandAbc9Bmc,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bmcs",         Abc_CommandAbc9SBmc,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&chainbmc",     Abc_CommandAbc9ChainBmc,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bcore",        Abc_CommandAbc9BCore,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&icheck",       Abc_CommandAbc9ICheck,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bmci",         Abc_CommandAbc9Bmci,         0 );
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
int Abc_CommandReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Saig_ParBbr_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarReach( Abc_Ntk_t * pNtk, Saig_ParBbr_t * pPars );

    // set defaults
    Bbr_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TBFLproyvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 )
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
        case 'p':
            pPars->fPartition ^= 1;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'o':
            pPars->fReorderImage ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
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
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The current network has no latches.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Reachability analysis works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    pAbc->Status  = Abc_NtkDarReach( pNtk, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "reach" );
    return 0;

usage:
    Abc_Print( -2, "usage: reach [-TBF num] [-L file] [-proyvh]\n" );
    Abc_Print( -2, "\t         verifies sequential miter using BDD-based reachability\n" );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-B num : max number of nodes in the intermediate BDDs [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-p     : enable partitioned image computation [default = %s]\n", pPars->fPartition? "yes": "no" );
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s]\n", pPars->fReorder? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggles BDD variable reordering during image computation [default = %s]\n", pPars->fReorderImage? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQuaReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nIters, fVerbose;
    extern Abc_Ntk_t * Abc_NtkReachability( Abc_Ntk_t * pNtk, int nIters, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nIters   = 256;
    fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ivh" ) ) != EOF )
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
    if ( Abc_NtkPoNum(pNtk) > 1 )
    {
        Abc_Print( -1, "The transition relation should have one output.\n" );
        return 1;
    }
    if ( Abc_NtkPiNum(pNtk) % 2 != 0 )
    {
        Abc_Print( -1, "The transition relation should have an even number of inputs.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkReachability( pNtk, nIters, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qreach [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         computes unreachable states using AIG-based quantification\n" );
    Abc_Print( -2, "\t         assumes that the current network is a transition relation\n" );
    Abc_Print( -2, "\t         assumes that the initial state is composed of all zeros\n" );
    Abc_Print( -2, "\t-I num : the number of image computations to perform [default = %d]\n", nIters );
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
int Abc_CommandDSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Fra_Sec_t SecPar, * pSecPar = &SecPar;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c, fCheck = 1;
    int fIgnoreNames;

    extern int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Fra_Sec_t * p );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Fra_SecSetDefaultParams( pSecPar );
    pSecPar->TimeLimit = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTarmfncvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nFramesMax < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->TimeLimit < 0 )
                goto usage;
            break;
        case 'a':
            pSecPar->fPhaseAbstract ^= 1;
            break;
        case 'r':
            pSecPar->fRetimeFirst ^= 1;
            break;
        case 'm':
            pSecPar->fRetimeRegs ^= 1;
            break;
        case 'f':
            pSecPar->fFraiging ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        case 'c':
            fCheck ^= 1;
            break;
        case 'v':
            pSecPar->fVerbose ^= 1;
            break;
        case 'w':
            pSecPar->fVeryVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, fCheck ) )
        return 1;
    if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
    {
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
        return 0;
    }

    if ( fIgnoreNames )
    {
        if ( !fDelete1 )
        {
            pNtk1 = Abc_NtkStrash( pNtk1, 0, 1, 0 );
            fDelete1 = 1;
        }
        if ( !fDelete2 )
        {
            pNtk2 = Abc_NtkStrash( pNtk2, 0, 1, 0 );
            fDelete2 = 1;
        }
        Abc_NtkShortNames( pNtk1 );
        Abc_NtkShortNames( pNtk2 );
    }

    // perform verification
    pAbc->Status = Abc_NtkDarSec( pNtk1, pNtk2, pSecPar );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dsec [-F num] [-T num] [-armfncvwh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs inductive sequential equivalence checking\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pSecPar->nFramesMax );
    Abc_Print( -2, "\t-T num : the approximate runtime limit (in seconds) [default = %d]\n", pSecPar->TimeLimit );
    Abc_Print( -2, "\t-a     : toggles the use of phase abstraction [default = %s]\n", pSecPar->fPhaseAbstract? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles forward retiming at the beginning [default = %s]\n", pSecPar->fRetimeFirst? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles min-register retiming [default = %s]\n", pSecPar->fRetimeRegs? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggles the internal use of fraiging [default = %s]\n", pSecPar->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggles how CIs/COs are matched (by name or by order) [default = %s]\n", fIgnoreNames? "by order": "by name" );
    Abc_Print( -2, "\t-c     : toggles performing internal netlist check [default = %s]\n", fCheck? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pSecPar->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles additional verbose output [default = %s]\n", pSecPar->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Fra_Sec_t SecPar, * pSecPar = &SecPar;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;
    int nBmcFramesMax = 20;
    int nBmcConfMax = 2000;

    extern void Fra_SecSetDefaultParams( Fra_Sec_t * p );
    extern int Abc_NtkDarProve( Abc_Ntk_t * pNtk, Fra_Sec_t * pSecPar, int nBmcFramesMax, int nBmcConfMax );
    // set defaults
    Fra_SecSetDefaultParams( pSecPar );
//    pSecPar->TimeLimit = 300;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cbAEFCGDVBRTLarmfijkoupwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            pSecPar->fTryComb ^= 1;
            break;
        case 'b':
            pSecPar->fTryBmc ^= 1;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nBmcFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBmcFramesMax < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nBmcConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBmcConfMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nFramesMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimit < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimitGlobal = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimitGlobal < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimitInter = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimitInter < 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddVarsMax < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddMax < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddIterMax < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nPdrTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nPdrTimeout < 0 )
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
            pSecPar->fPhaseAbstract ^= 1;
            break;
        case 'r':
            pSecPar->fRetimeFirst ^= 1;
            break;
        case 'm':
            pSecPar->fRetimeRegs ^= 1;
            break;
        case 'f':
            pSecPar->fFraiging ^= 1;
            break;
        case 'i':
            pSecPar->fInduction ^= 1;
            break;
        case 'j':
            pSecPar->fInterpolation ^= 1;
            break;
        case 'k':
            pSecPar->fInterSeparate ^= 1;
            break;
        case 'o':
            pSecPar->fReorderImage ^= 1;
            break;
        case 'u':
            pSecPar->fReadUnsolved ^= 1;
            break;
        case 'p':
            pSecPar->fUsePdr ^= 1;
            break;
        case 'w':
            pSecPar->fVeryVerbose ^= 1;
            break;
        case 'v':
            pSecPar->fVerbose ^= 1;
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
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }

    // perform verification
    pAbc->Status = Abc_NtkDarProve( pNtk, pSecPar, nBmcFramesMax, nBmcConfMax );
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "dprove" );

    // read back the resulting unsolved reduced sequential miter
    if ( pSecPar->fReadUnsolved && pSecPar->nSMnumber >= 0 )
    {
        char FileName[100];
        sprintf(FileName, "sm%02d.aig", pSecPar->nSMnumber );
        pNtk = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
        if ( pNtk == NULL )
            Abc_Print( -1, "Cannot read back unsolved reduced sequential miter \"%s\",\n", FileName );
        else
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dprove [-AEFCGDVBRT num] [-L file] [-cbarmfijoupvwh]\n" );
    Abc_Print( -2, "\t         performs SEC on the sequential miter\n" );
    Abc_Print( -2, "\t-A num : the limit on the depth of BMC [default = %d]\n", nBmcFramesMax );
    Abc_Print( -2, "\t-E num : the conflict limit during BMC [default = %d]\n", nBmcConfMax );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pSecPar->nFramesMax );
    Abc_Print( -2, "\t-C num : the conflict limit at a node during induction [default = %d]\n", pSecPar->nBTLimit );
    Abc_Print( -2, "\t-G num : the global conflict limit during induction [default = %d]\n", pSecPar->nBTLimitGlobal );
    Abc_Print( -2, "\t-D num : the conflict limit during interpolation [default = %d]\n", pSecPar->nBTLimitInter );
    Abc_Print( -2, "\t-V num : the flop count limit for BDD-based reachablity [default = %d]\n", pSecPar->nBddVarsMax );
    Abc_Print( -2, "\t-B num : the BDD size limit in BDD-based reachablity [default = %d]\n", pSecPar->nBddMax );
    Abc_Print( -2, "\t-R num : the max number of reachability iterations [default = %d]\n", pSecPar->nBddIterMax );
    Abc_Print( -2, "\t-T num : the timeout for property directed reachability [default = %d]\n", pSecPar->nPdrTimeout );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-c     : toggles using CEC before attempting SEC [default = %s]\n", pSecPar->fTryComb? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles using BMC before attempting SEC [default = %s]\n", pSecPar->fTryBmc? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggles the use of phase abstraction [default = %s]\n", pSecPar->fPhaseAbstract? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles forward retiming at the beginning [default = %s]\n", pSecPar->fRetimeFirst? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles min-register retiming [default = %s]\n", pSecPar->fRetimeRegs? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggles the internal use of fraiging [default = %s]\n", pSecPar->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggles the use of induction [default = %s]\n", pSecPar->fInduction? "yes": "no" );
    Abc_Print( -2, "\t-j     : toggles the use of interpolation [default = %s]\n", pSecPar->fInterpolation? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggles applying interpolation to each output [default = %s]\n", pSecPar->fInterSeparate? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggles using BDD variable reordering during image computation [default = %s]\n", pSecPar->fReorderImage? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggles reading back unsolved reduced sequential miter [default = %s]\n", pSecPar->fReadUnsolved? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggles trying property directed reachability in the end [default = %s]\n", pSecPar->fUsePdr? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pSecPar->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles additional verbose output [default = %s]\n", pSecPar->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tCommand \"dprove\" can also be used for sequential synthesis (dprove -brjopu)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int fMiter, nFrames, fVerbose, c;

    extern int Abc_NtkDarAbSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter   = 1;
    nFrames  = 2;
    fVerbose = 0;
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
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 )
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fMiter )
    {
//        pNtk = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1, 0 );
        if ( argc == globalUtilOptind + 1 )
        {
            Abc_Print( -1, "The miter cannot be given on the command line. Use \"read\".\n" );
            return 0;
        }
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "The miter should be structurally hashed. Use \"st\"\n" );
            return 0;
        }
        if ( Abc_NtkDarAbSec( pNtk, NULL, nFrames, fVerbose ) == 1 )
            pAbc->Status = 1;
        else
            pAbc->Status = -1;
    }
    else
    {
        pArgvNew = argv + globalUtilOptind;
        nArgcNew = argc - globalUtilOptind;
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
            return 0;
        }
        // perform verification
        if ( Abc_NtkDarAbSec( pNtk1, pNtk2, nFrames, fVerbose ) == 1 )
            pAbc->Status = 1;
        else
            pAbc->Status = -1;
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: absec [-F num] [-mv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs SEC by applying CEC to several timeframes\n" );
    Abc_Print( -2, "\t-F num : the total number of timeframes to use [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-m     : toggles miter vs. two networks [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSimSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Ssw_Pars_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew, c;
    int fMiter;

    extern int Abc_NtkDarSimSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Ssw_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter = 1;
    Ssw_ManSetDefaultParams( pPars );
    pPars->fPartSigCorr = 1;
    pPars->fVerbose     = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FDcymvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIsleDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIsleDist < 0 )
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'c':
            pPars->fPartSigCorr ^= 1;
            break;
        case 'y':
            pPars->fDumpSRInit ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fMiter )
    {
//        Abc_Ntk_t * pNtkA, * pNtkB;
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
            return 0;
        }
        Abc_NtkDarSimSec( pNtk, NULL, pPars );
//        pNtkA = Abc_NtkDup( pNtk );
//        pNtkB = Abc_NtkDup( pNtk );
//        Abc_NtkDarSimSec( pNtkA, pNtkB, pPars );
//        Abc_NtkDelete( pNtkA );
//        Abc_NtkDelete( pNtkB );
    }
    else
    {
        pArgvNew = argv + globalUtilOptind;
        nArgcNew = argc - globalUtilOptind;
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
            return 0;
        }
        // perform verification
        Abc_NtkDarSimSec( pNtk1, pNtk2, pPars );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: simsec [-FD num] [-mcyv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs SEC using structural similarity\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-D num : the distance for extending islands [default = %d]\n", pPars->nIsleDist );
    Abc_Print( -2, "\t-m     : toggles miter vs. two networks [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-c     : uses partial vs. full signal correspondence [default = %s]\n", pPars->fPartSigCorr? "partial": "full" );
    Abc_Print( -2, "\t-y     : dumps speculatively reduced miter of the classes [default = %s]\n", pPars->fDumpSRInit? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int nSizeMax;
    int nBTLimit;
    int nBTLimitAll;
    int nNodeDelta;
    int fRewrite;
    int fNewAlgo;
    int nCofFanLit;
    int fVerbose;
    int iFrames;
    int fUseSatoko;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nStart, int nFrames, int nSizeMax, int nNodeDelta, int nTimeOut, int nBTLimit, int nBTLimitAll, int fRewrite, int fNewAlgo, int fOrDecomp, int nCofFanLit, int fVerbose, int * piFrames, int fUseSatoko );
    // set defaults
    nFrames     =       20;
    nSizeMax    =   100000;
    nBTLimit    =        0;
    nBTLimitAll =        0;
    nNodeDelta  =     1000;
    fRewrite    =        0;
    fNewAlgo    =        1;
    nCofFanLit  =        0;
    fVerbose    =        0;
    fUseSatoko  =        0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FNCGDLrsvh" ) ) != EOF )
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSizeMax < 0 )
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
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimitAll = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimitAll < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeDelta < 0 )
                goto usage;
            break;
//        case 'L':
//            if ( globalUtilOptind >= argc )
//            {
//                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
//                goto usage;
//            }
//            nCofFanLit = atoi(argv[globalUtilOptind]);
//            globalUtilOptind++;
//            if ( nCofFanLit < 0 )
//                goto usage;
//            break;
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
            fRewrite ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    pAbc->Status = Abc_NtkDarBmc( pNtk, 0, nFrames, nSizeMax, nNodeDelta, 0, nBTLimit, nBTLimitAll, fRewrite, fNewAlgo, 0, nCofFanLit, fVerbose, &iFrames, fUseSatoko );
    pAbc->nFrames = iFrames;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc" );
    return 0;

usage:
    Abc_Print( -2, "usage: bmc [-FNC num] [-L file] [-rcsvh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with static unrolling\n" );
    Abc_Print( -2, "\t-F num : the number of time frames [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-N num : the max number of nodes in the frames [default = %d]\n", nSizeMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
//    Abc_Print( -2, "\t-L num : the limit on fanout count of resets/enables to cofactor [default = %d]\n", nCofFanLit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", fRewrite? "yes": "no" );
//    Abc_Print( -2, "\t-a     : toggle SAT sweeping and SAT solving [default = %s]\n", fNewAlgo? "SAT solving": "SAT sweeping" );
    Abc_Print( -2, "\t-s     : toggle using Satoko by Bruno Schmitt [default = %s]\n", fUseSatoko? "yes": "no" );
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
int Abc_CommandBmc2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nStart;
    int nFrames;
    int nSizeMax;
    int nBTLimit;
    int nBTLimitAll;
    int nNodeDelta;
    int nTimeOut;
    int fRewrite;
    int fNewAlgo;
    int fOrDecomp;
    int fVerbose;
    int iFrames;
    int fUseSatoko;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nStart, int nFrames, int nSizeMax, int nNodeDelta, int nTimeOut, int nBTLimit, int nBTLimitAll, int fRewrite, int fNewAlgo, int fOrDecomp, int nCofFanLit, int fVerbose, int * piFrames, int fUseSatoko );

    // set defaults
    nStart      =        0;
    nFrames     =        0;
    nSizeMax    =   200000;
    nBTLimit    =        0;
    nBTLimitAll =        0;
    nNodeDelta  =     2000;
    nTimeOut    =        0;
    fRewrite    =        0;
    fNewAlgo    =        0;
    fOrDecomp   =        0;
    fVerbose    =        0;
    fUseSatoko  =        0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFNTCGDLrusvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStart < 0 )
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSizeMax < 0 )
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
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimitAll = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimitAll < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeDelta < 0 )
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
            fRewrite ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'u':
            fOrDecomp ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    pAbc->Status = Abc_NtkDarBmc( pNtk, nStart, nFrames, nSizeMax, nNodeDelta, nTimeOut, nBTLimit, nBTLimitAll, fRewrite, fNewAlgo, fOrDecomp, 0, fVerbose, &iFrames, fUseSatoko );
    pAbc->nFrames = iFrames;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc2" );
    return 0;

usage:
    Abc_Print( -2, "usage: bmc2 [-SFTCGD num] [-L file] [-usvh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with dynamic unrolling\n" );
    Abc_Print( -2, "\t-S num : the starting time frame [default = %d]\n", nStart );
    Abc_Print( -2, "\t-F num : the max number of time frames (0 = unused) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-G num : the max number of conflicts globally [default = %d]\n", nBTLimitAll );
    Abc_Print( -2, "\t-D num : the delta in the number of nodes [default = %d]\n", nNodeDelta );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-u     : toggle performing structural OR-decomposition [default = %s]\n", fOrDecomp? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using Satoko by Bruno Schmitt [default = %s]\n", fUseSatoko? "yes": "no" );
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
int Abc_CommandBmc3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkDarBmc3( Abc_Ntk_t * pNtk, Saig_ParBmc_t * pPars, int fOrDecomp );
    Saig_ParBmc_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    Vec_Ptr_t * vSeqModelVec = NULL;
    Vec_Int_t * vStatuses = NULL;
    char * pLogFileName = NULL;
    int fOrDecomp = 0;
    int c;
    Saig_ParBmcSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFTHGCDJIPQRLWaxdursgvzhc" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 )
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
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOutOne = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOutOne < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOutGap = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOutGap < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimitJump = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimitJump < 0 )
                goto usage;
            break;
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesJump = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesJump < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPisAbstract = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPisAbstract < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedStart < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedDelta < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedPerce = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedPerce < 0 )
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
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'a':
            pPars->fSolveAll ^= 1;
            break;
        case 'x':
            pPars->fStoreCex ^= 1;
            break;
        case 'd':
            pPars->fDropSatOuts ^= 1;
            break;
        case 'u':
            fOrDecomp ^= 1;
            break;
        case 'r':
            pPars->fNoRestarts ^= 1;
            break;
        case 's':
            pPars->fUseSatoko ^= 1;
            break;
        case 'g':
            pPars->fUseGlucose ^= 1;
            break;
        case 'c':
            pPars->fUseCadical ^= 1;
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
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Constraints have to be folded (use \"fold\").\n" );
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    pPars->fUseBridge = pAbc->fBridgeMode;
    pAbc->Status = Abc_NtkDarBmc3( pNtk, pPars, fOrDecomp );
    pAbc->nFrames = pNtk->vSeqModelVec ? -1 : pPars->iFrame;
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc3" );
    vSeqModelVec = pNtk->vSeqModelVec;  pNtk->vSeqModelVec = NULL;
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
    vStatuses = Abc_FrameDeriveStatusArray( vSeqModelVec );
    Abc_FrameReplacePoStatuses( pAbc, &vStatuses );
    if ( vSeqModelVec )
        Abc_FrameReplaceCexVec( pAbc, &vSeqModelVec );
    else
        Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    return 0;

usage:
    Abc_Print( -2, "usage: bmc3 [-SFTHGCDJIPQR num] [-LW file] [-axdursgvzh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with dynamic unrolling\n" );
    Abc_Print( -2, "\t-S num : the starting time frame [default = %d]\n", pPars->nStart );
    Abc_Print( -2, "\t-F num : the max number of time frames (0 = unused) [default = %d]\n",      pPars->nFramesMax );
    Abc_Print( -2, "\t-T num : runtime limit, in seconds [default = %d]\n",                       pPars->nTimeOut );
    Abc_Print( -2, "\t-H num : runtime limit per output, in milliseconds (with \"-a\") [default = %d]\n",    pPars->nTimeOutOne );
    Abc_Print( -2, "\t-G num : runtime gap since the last CEX, in seconds [default = %d]\n",      pPars->nTimeOutGap );
    Abc_Print( -2, "\t-C num : max conflicts at an output [default = %d]\n",                      pPars->nConfLimit );
    Abc_Print( -2, "\t-D num : max conflicts after jumping (0 = infinity) [default = %d]\n",      pPars->nConfLimitJump );
    Abc_Print( -2, "\t-J num : the number of timeframes to jump (0 = not used) [default = %d]\n", pPars->nFramesJump );
    Abc_Print( -2, "\t-I num : the number of PIs to abstract [default = %d]\n",                   pPars->nPisAbstract );
    Abc_Print( -2, "\t-P num : the max number of learned clauses to keep (0=unused) [default = %d]\n", pPars->nLearnedStart );
    Abc_Print( -2, "\t-Q num : delta value for learned clause removal [default = %d]\n",          pPars->nLearnedDelta );
    Abc_Print( -2, "\t-R num : percentage to keep for learned clause removal [default = %d]\n",   pPars->nLearnedPerce );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n",                               pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-W file: the log file name with per-output details [default = %s]\n",       pPars->pLogFileName ? pPars->pLogFileName : "no logging" );
    Abc_Print( -2, "\t-a     : solve all outputs (do not stop when one is SAT) [default = %s]\n", pPars->fSolveAll? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle storing CEXes when solving all outputs [default = %s]\n",   pPars->fStoreCex? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dropping (replacing by 0) SAT outputs [default = %s]\n",    pPars->fDropSatOuts? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle performing structural OR-decomposition [default = %s]\n",   fOrDecomp? "yes": "not" );
    Abc_Print( -2, "\t-r     : toggle disabling periodic restarts [default = %s]\n",              pPars->fNoRestarts? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using Satoko by Bruno Schmitt [default = %s]\n", pPars->fUseSatoko? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n",pPars->fUseGlucose? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using CaDiCaL by Armin Biere, University of Freiburg [default = %s]\n",pPars->fUseCadical? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n",                           pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle suppressing report about solved outputs [default = %s]\n",  pPars->fNotVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmcInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Inter_ManParams_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmcInter( Abc_Ntk_t * pNtk, Inter_ManParams_t * pPars, Abc_Ntk_t ** ppNtkRes );
    // set defaults
    Inter_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CFTKLIrtpomcgbqkdivh" ) ) != EOF )
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
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSecLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSecLimit < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK < 0 )
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 't':
            pPars->fTransLoop ^= 1;
            break;
        case 'p':
            pPars->fUsePudlak ^= 1;
            break;
        case 'o':
            pPars->fUseOther ^= 1;
            break;
        case 'm':
            pPars->fUseMiniSat ^= 1;
            break;
        case 'c':
            pPars->fCheckKstep ^= 1;
            break;
        case 'g':
            pPars->fUseBias ^= 1;
            break;
        case 'b':
            pPars->fUseBackward ^= 1;
            break;
        case 'q':
            pPars->fUseTwoFrames ^= 1;
            break;
        case 'k':
            pPars->fUseSeparate ^= 1;
            break;
        case 'd':
            pPars->fDropSatOuts ^= 1;
            break;
        case 'i':
            pPars->fDropInvar ^= 1;
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
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Cannot run interpolation with constraints. Use \"fold\".\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk)-Abc_NtkConstrNum(pNtk) != 1 )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
        {
            Abc_Print( 1,"Cannot solve multiple-output miter with constraints.\n" );
            return 0;
        }
        if ( pPars->fUseSeparate )
        {
            Abc_Print( 0, "Each of %d outputs will be solved separately.\n", Abc_NtkPoNum(pNtk) );
            pAbc->Status = Abc_NtkDarBmcInter( pNtk, pPars, &pNtkRes );
            Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
            if ( pNtkRes == NULL )
            {
                Abc_Print( -1, "Generating resulting network has failed.\n" );
                return 0;
            }
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        }
        else
        {
            Abc_Ntk_t * pNtkNew = Abc_NtkDup( pNtk );
            Abc_Print( 0, "All %d outputs will be ORed together.\n", Abc_NtkPoNum(pNtk) );
            if ( !Abc_NtkCombinePos( pNtkNew, 0, 0 ) )
            {
                Abc_NtkDelete( pNtkNew );
                Abc_Print( -1, "ORing outputs has failed.\n" );
                return 0;
            }
            pAbc->Status = Abc_NtkDarBmcInter( pNtkNew, pPars, NULL );
            if ( pAbc->Status == 0 )
            {
                Aig_Man_t * pMan = Abc_NtkToDar( pNtk, 0, 1 );
                pNtkNew->pSeqModel->iPo = Saig_ManFindFailedPoCex( pMan, pNtkNew->pSeqModel );
                Aig_ManStop( pMan );
            }
            Abc_FrameReplaceCex( pAbc, &pNtkNew->pSeqModel );
            Abc_NtkDelete( pNtkNew );
        }
        pAbc->nFrames = -1;
    }
    else
    {
        pAbc->Status  = Abc_NtkDarBmcInter( pNtk, pPars, NULL );
        pAbc->nFrames = pPars->iFrameMax;
        Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    }
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "int" );
    return 0;

usage:
    Abc_Print( -2, "usage: int [-CFTK num] [-LI file] [-irtpomcgbqkdvh]\n" );
    Abc_Print( -2, "\t         uses interpolation to prove the property\n" );
    Abc_Print( -2, "\t-C num : the limit on conflicts for one SAT run [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the limit on number of frames to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-T num : the limit on runtime per output in seconds [default = %d]\n", pPars->nSecLimit );
    Abc_Print( -2, "\t-K num : the number of steps in inductive checking [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t         (K = 1 works in all cases; K > 1 works without -t and -b)\n" );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-I file: the file name for dumping interpolant [default = \"%s\"]\n", pPars->pFileName ? pPars->pFileName : "invar.aig" );
    Abc_Print( -2, "\t-i     : toggle dumping interpolant/invariant into a file [default = %s]\n", pPars->fDropInvar? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle rewriting of the unrolled timeframes [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle adding transition into the initial state [default = %s]\n", pPars->fTransLoop? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle using original Pudlak's interpolation procedure [default = %s]\n", pPars->fUsePudlak? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using optimized Pudlak's interpolation procedure [default = %s]\n", pPars->fUseOther? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using MiniSat-1.14p (now, Windows-only) [default = %s]\n", pPars->fUseMiniSat? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using inductive containment check [default = %s]\n", pPars->fCheckKstep? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using bias for global variables using SAT [default = %s]\n", pPars->fUseBias? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle using backward interpolation (works with -t) [default = %s]\n", pPars->fUseBackward? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle using property in two last timeframes [default = %s]\n", pPars->fUseTwoFrames? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle solving each output separately [default = %s]\n", pPars->fUseSeparate? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dropping (replacing by 0) SAT outputs (with -k is used) [default = %s]\n", pPars->fDropSatOuts? "yes": "no" );
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
int Abc_CommandIndcut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nFrames;
    int nPref;
    int nClauses;
    int nLutSize;
    int nLevels;
    int nCutsMax;
    int nBatches;
    int fStepUp;
    int fBmc;
    int fRegs;
    int fTarget;
    int fVerbose;
    int fVeryVerbose;
    int c;
    extern int Abc_NtkDarClau( Abc_Ntk_t * pNtk, int nFrames, int nPref, int nClauses, int nLutSize, int nLevels, int nCutsMax, int nBatches, int fStepUp, int fBmc, int fRegs, int fTarget, int fVerbose, int fVeryVerbose );
    // set defaults
    nFrames      =    1;
    nPref        =    0;
    nClauses     = 5000;
    nLutSize     =    4;
    nLevels      =    8;
    nCutsMax     =   16;
    nBatches     =    1;
    fStepUp      =    0;
    fBmc         =    1;
    fRegs        =    1;
    fTarget      =    1;
    fVerbose     =    0;
    fVeryVerbose =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FPCMLNBsbrtvwh" ) ) != EOF )
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
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nClauses = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nClauses < 0 )
                goto usage;
            break;
        case 'M':
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
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBatches = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBatches < 0 )
                goto usage;
            break;
        case 's':
            fStepUp ^= 1;
            break;
        case 'b':
            fBmc ^= 1;
            break;
        case 'r':
            fRegs ^= 1;
            break;
        case 't':
            fTarget ^= 1;
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
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( nLutSize > 12 )
    {
        Abc_Print( -1, "The cut size should be not exceed 12.\n" );
        return 0;
    }
    Abc_NtkDarClau( pNtk, nFrames, nPref, nClauses, nLutSize, nLevels, nCutsMax, nBatches, fStepUp, fBmc, fRegs, fTarget, fVerbose, fVeryVerbose );
    return 0;
usage:
    Abc_Print( -2, "usage: indcut [-FPCMLNB num] [-sbrtvh]\n" );
    Abc_Print( -2, "\t         K-step induction strengthened with cut properties\n" );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-P num : number of time frames in the prefix (0=no prefix) [default = %d]\n", nPref );
    Abc_Print( -2, "\t-C num : the max number of clauses to use for strengthening [default = %d]\n", nClauses );
    Abc_Print( -2, "\t-M num : the cut size (2 <= M <= 12) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-L num : the max number of levels for cut computation [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-N num : the max number of cuts to compute at a node [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-B num : the max number of invariant batches to try [default = %d]\n", nBatches );
    Abc_Print( -2, "\t-s     : toggle increment cut size in each batch [default = %s]\n", fStepUp? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle enabling BMC check [default = %s]\n", fBmc? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle enabling register clauses [default = %s]\n", fRegs? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle proving target / computing don't-cares [default = %s]\n", fTarget? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandInduction( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nTimeOut;
    int nFramesMax;
    int nConfMax;
    int fUnique;
    int fUniqueAll;
    int fGetCex;
    int fVerbose;
    int fVeryVerbose;
    int c;
    extern int Abc_NtkDarInduction( Abc_Ntk_t * pNtk, int nTimeOut, int nFramesMax, int nConfMax, int fUnique, int fUniqueAll, int fGetCex, int fVerbose, int fVeryVerbose );
    // set defaults
    nTimeOut     =     0;
    nFramesMax   =     0;
    nConfMax     =     0;
    fUnique      =     0;
    fUniqueAll   =     0;
    fGetCex      =     0;
    fVerbose     =     0;
    fVeryVerbose =     0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCTuaxvwh" ) ) != EOF )
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
        case 'u':
            fUnique ^= 1;
            break;
        case 'a':
            fUniqueAll ^= 1;
            break;
        case 'x':
            fGetCex ^= 1;
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
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently this command works only for single-output miter.\n" );
        return 0;
    }
    if ( fUnique && fUniqueAll )
    {
        Abc_Print( -1, "Only one of the options, \"-u\" or \"-a\", should be selected.\n" );
        return 0;
    }

    // modify the current network
    pAbc->Status = Abc_NtkDarInduction( pNtk, nTimeOut, nFramesMax, nConfMax, fUnique, fUniqueAll, fGetCex, fVerbose, fVeryVerbose );
    if ( fGetCex )
    {
        Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
        Abc_Print( 1,"The current CEX in ABC is set to be the CEX to induction.\n" );
    }
    return 0;
usage:
    Abc_Print( -2, "usage: ind [-FCT num] [-uaxvwh]\n" );
    Abc_Print( -2, "\t         runs the inductive case of the K-step induction\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes [default = %d]\n", nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts by SAT solver [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-T num : the limit on runtime per output in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-u     : toggle adding uniqueness constraints on demand [default = %s]\n", fUnique? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle adding uniqueness constraints always [default = %s]\n", fUniqueAll? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle returning CEX to induction for the top frame [default = %s]\n", fGetCex? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing additional verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPdr2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkDarPdr2( Abc_Ntk_t * pNtk, Pdr2_Par_t * pPars );
    Pdr2_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkUsed, * pNtkFlop = NULL;
    char * pLogFileName = NULL;
    int c;
    Pdr2_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTSXYANZQDERCPMGKUJHLIcgopluktedrbxjsOBWVmfqianvywzh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrameMax < 0 )
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRandomSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRandomSeed < 0 )
                goto usage;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCtgMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCtgMax < 0 )
                goto usage;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCtgLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCtgLimit < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nAbsStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAbsStart < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLiftIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLiftIters < -1 )
                goto usage;
            break;
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDynLimitMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDynLimitMax < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDynAct = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDynAct < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDynTime = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDynTime < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDynExplode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDynExplode < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLevelRestart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLevelRestart < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCtgTime = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCtgTime < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPreprocTime = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPreprocTime < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nAbsTime = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAbsTime < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nAbsRefineMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAbsRefineMode < 0 || pPars->nAbsRefineMode > 3 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nQueueOrder = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nQueueOrder < 0 || pPars->nQueueOrder > 3 )
                goto usage;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLiftSim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLiftSim < 0 || pPars->nLiftSim > 2 )
                goto usage;
            break;
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLiftSimOrder = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLiftSimOrder < 0 || pPars->nLiftSimOrder > 2 )
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMicMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMicMode < 0 || pPars->nMicMode > 1 )
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pInvFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'c':
            pPars->fCtg ^= 1;
            break;
        case 'g':
            pPars->fDynamic ^= 1;
            break;
        case 'o':
            pPars->fDropPo ^= 1;
            break;
        case 'p':
            pPars->fParentLemma ^= 1;
            break;
        case 'l':
            pPars->fLift ^= 1;
            break;
        case 'u':
            pPars->fPropHyp ^= 1;
            break;
        case 'k':
            pPars->fCtiCache ^= 1;
            break;
        case 't':
            pPars->fUseAbs ^= 1;
            break;
        case 'e':
            pPars->fAbsCleanup ^= 1;
            break;
        case 'r':
            pPars->fAbsRefineAll ^= 1;
            break;
        case 'b':
            pPars->fAbsReset ^= 1;
            break;
        case 'x':
            pPars->fAbsRefineXsim ^= 1;
            break;
        case 'j':
            pPars->fTopCtg ^= 1;
            break;
        case 's':
            pPars->fSemContain ^= 1;
            break;
        case 'f':
            pPars->fDynFirst ^= 1;
            break;
        case 'q':
            pPars->fPreproc ^= 1;
            break;
        case 'i':
            pPars->fBlockInduct ^= 1;
            break;
        case 'a':
            pPars->nQueueOrder ^= 1;
            break;
        case 'n':
            pPars->fShareInf ^= 1;
            break;
        case 'm':
            pPars->fCtgMic ^= 1;
            break;
        case 'O':
            pPars->fKeepObl ^= 1;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nAbsRuns = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAbsRuns < 0 || pPars->nAbsRuns > 2 )
                goto usage;
            break;
        case 'W':
            pPars->fInfPromote ^= 1;
            break;
        case 'V':
            pPars->fSimRun ^= 1;
            break;
        case 'y':
            pPars->fVerify ^= 1;
            break;
        case 'd':
            pPars->fDumpInv ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'z':
            pPars->fSilent ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    // with the abstraction, relative induction in the blocking query is on by default (-i then turns it off)
    if ( pPars->fUseAbs )
        pPars->fBlockInduct ^= 1;
    if ( pNtk == NULL )
    {
        Abc_Print( -2, "There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -2, "The current network is not an AIG (run \"strash\").\n");
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) )
    {
        Abc_Print( 1, "The miter is already solved; skipping the command.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        // (a dummy flop initialized to 0, so that the initial values stay all 0)
        pNtkFlop = Abc_NtkDup( pNtk );
        Abc_NtkAddLatch( pNtkFlop, Abc_ObjNot(Abc_AigConst1(pNtkFlop)), ABC_INIT_ZERO );
    }
    // run the procedure
    pNtkUsed = pNtkFlop ? pNtkFlop : pNtk;
    pAbc->Status  = Abc_NtkDarPdr2( pNtkUsed, pPars );
    pAbc->nFrames = pPars->iFrame;
    if ( pNtkFlop && pNtkUsed->pSeqModel )
    {
        // the counterexample of a combinational network: drop the bit of the added latch
        Abc_Cex_t * pCex = Abc_CexDup( pNtkUsed->pSeqModel, 0 );
        Abc_CexFree( pNtkUsed->pSeqModel );
        pNtkUsed->pSeqModel = pCex;
    }
    Abc_FrameReplaceCex( pAbc, &pNtkUsed->pSeqModel );
    if ( pNtkFlop ) Abc_NtkDelete( pNtkFlop );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "pdr2" );
    return 0;

usage:
    Abc_Print( -2, "usage: pdr2 [-FTSXYANZQDERCPMGKUJHB <num>] [-LI <file>] [-cgopluktedrbxjsOWVmfqianvywzh]\n" );
    Abc_Print( -2, "\t         model checking using property directed reachability (aka IC3)\n" );
    Abc_Print( -2, "\t         with SAT-core lifting, CTG generalization, and the GipSAT solver\n" );
    Abc_Print( -2, "\t         (the algorithm follows rIC3 by Yuheng Su, https://github.com/gipsyh/rIC3)\n" );
    Abc_Print( -2, "\t-F num : limit on timeframes explored to stop computation [default = %d]\n",           pPars->nFrameMax );
    Abc_Print( -2, "\t-T num : runtime limit, in seconds (0 = no limit) [default = %d]\n",                   pPars->nTimeOut );
    Abc_Print( -2, "\t-S num : random seed [default = %d]\n",                                                pPars->nRandomSeed );
    Abc_Print( -2, "\t-X num : max number of CTGs handled per literal drop [default = %d]\n",                pPars->nCtgMax );
    Abc_Print( -2, "\t-Y num : effort limit on blocking CTGs [default = %d]\n",                              pPars->nCtgLimit );
    Abc_Print( -2, "\t-A num : start the abstraction after this many seconds [default = %d]\n",            pPars->nAbsStart );
    Abc_Print( -2, "\t-N num : max number of lifting iterations (0 = until no change, -1 = no SAT lifting) [default = %d]\n",   pPars->nLiftIters );
    Abc_Print( -2, "\t-Z num : cap on the CTG blocking effort in dynamic mode [default = %d]\n",            pPars->nDynLimitMax );
    Abc_Print( -2, "\t-Q num : obligation activity threshold for CTG in dynamic mode [default = %d]\n",     pPars->nDynAct );
    Abc_Print( -2, "\t-D num : first budget of the dynamic phases, in nominal seconds (12 M solver propagations each); phases alternate and double (0 = dynamic only; the plain dynamic run needs PDR2_DYNRUN=1) [default = %d]\n", pPars->nDynTime );
    Abc_Print( -2, "\t-C num : first budget of the CTG phases, in nominal seconds (12 M solver propagations each) [default = %d]\n", pPars->nCtgTime );
    Abc_Print( -2, "\t-E num : end a dynamic phase when a level handles this many obligations (and 3x the previous max; 0 = never) [default = %d]\n", pPars->nDynExplode );
    Abc_Print( -2, "\t-R num : restart the obligation queue when a level has used this many millions of solver propagations (the budget doubles; 0 = never) [default = %d]\n", pPars->nLevelRestart );
    Abc_Print( -2, "\t-P num : time limit (sec) of the scorr preprocessing (with -q) [default = %d]\n", pPars->nPreprocTime );
    Abc_Print( -2, "\t-M num : first budget of the abstraction runs (with -t, -B, -V), in nominal seconds (12 M solver propagations each) [default = %d]\n", pPars->nAbsTime );
    Abc_Print( -2, "\t-G num : refinement variant: 0 = recorded pseudo-inputs, 1 = all outside flops fixed, 2 = treb's loop, 3 = 2 + intermediate frames [default = %d]\n", pPars->nAbsRefineMode );
    Abc_Print( -2, "\t-K num : obligation order in a frame: 0 = deepest chain first, 1 = shortest cube first, 2 = most recently queued first, 3 = shortest, then most recently queued [default = %d]\n", pPars->nQueueOrder );
    Abc_Print( -2, "\t-U num : weaken predecessors by justification and ternary simulation: 0 = no, 1 = before the SAT core, 2 = instead of it [default = %d]\n", pPars->nLiftSim );
    Abc_Print( -2, "\t-J num : order of the removal trials: 0 = highest activity first, 1 = lowest first, 2 = by flop index [default = %d]\n", pPars->nLiftSimOrder );
    Abc_Print( -2, "\t-H num : generalization: 0 = MIC with down/CTG (rIC3), 1 = two-orbit literal removal with core shrinking (treb) [default = %d]\n", pPars->nMicMode );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n",                                          pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-I file: the invariant file name; the design is written as <name>_design.aig [default = %s]\n", pPars->pInvFileName ? pPars->pInvFileName : "inv.pla" );
    Abc_Print( -2, "\t-c     : toggle generalization with counterexamples to generalization [default = %s]\n", pPars->fCtg? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle choosing CTG effort from obligation activity (no dropping) [default = %s]\n", pPars->fDynamic? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle dropping proof obligations that keep failing [default = %s]\n",        pPars->fDropPo? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle ordering literals by the parent lemma [default = %s]\n",               pPars->fParentLemma? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle cheap model-based lifting before the SAT-core lift [default = %s]\n",  pPars->fLift? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle asserting the property in completed frames [default = %s]\n",           pPars->fPropHyp? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle caching counterexamples to propagation [default = %s]\n",              pPars->fCtiCache? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle localization abstraction of flops [default = %s]\n",                  pPars->fUseAbs? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle removing unused flops from the abstraction [default = %s]\n",       pPars->fAbsCleanup? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle refining with all pseudo-inputs of a spurious CEX [default = %s]\n",  pPars->fAbsRefineAll? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle gating flop outputs with a reset flop (with -t) [default = %s]\n",    pPars->fAbsReset? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle refining by ternary-simulation minimization [default = %s]\n",      pPars->fAbsRefineXsim? "yes": "no" );
    Abc_Print( -2, "\t-j     : toggle minimum CTG effort for top-level obligations [default = %s]\n",       pPars->fTopCtg? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle the semantic containment check of obligations [default = %s]\n",     pPars->fSemContain? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle starting with a dynamic phase instead of a CTG phase (with -t or PDR2_DYNRUN=1) [default = %s]\n", pPars->fDynFirst? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle simplifying the design with signal correspondence (scorr) first [default = %s]\n", pPars->fPreproc? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle assuming the negation of the cube in the blocking query [default = %s; yes with -t]\n", pPars->fBlockInduct? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle treb's obligation order (shortest cube first) instead of deepest chain first [default = %s]\n", pPars->nQueueOrder? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle passing invariant lemmas between runs 0 and 1 (with -t or PDR2_DYNRUN=1) [default = %s]\n", pPars->fShareInf? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle generalizing the lemmas that block CTGs [default = %s]\n", pPars->fCtgMic? "yes": "no" );
    Abc_Print( -2, "\t-O     : toggle keeping obligations pushed beyond the last frame [default = %s]\n",   pPars->fKeepObl? "yes": "no" );
    Abc_Print( -2, "\t-B num : abstraction runs added to the alternating schedule (0 = none, 1 = dynamic, 2 = also CTG generalization) [default = %d]\n", pPars->nAbsRuns );
    Abc_Print( -2, "\t-W     : toggle moving new lemmas to frame infinity when inductive relative to it [default = %s]\n", pPars->fInfPromote? "yes": "no" );
    Abc_Print( -2, "\t-V     : toggle running CTG generalization with the weakening by simulation as another alternating run [default = %s]\n", pPars->fSimRun? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle verifying the inductive invariant [default = %s]\n",                    pPars->fVerify? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dumping the inductive invariant (with the solved design, see -I) [default = %s]\n", pPars->fDumpInv? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",                        pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n",                   pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle suppressing report about solved outputs [default = %s]\n",             pPars->fSilent? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t         environment: PDR2_BMC=<sec> time limit of the BMC stage after the first slice (0 = none) [default = %d],\n", pPars->nBmcTime );
    Abc_Print( -2, "\t         PDR2_TIMEGEN=0|1|2 time generalization (off, frame infinity only, also frame jumps) [default = %d],\n", pPars->fTimeGen );
    Abc_Print( -2, "\t         PDR2_DYNRUN=0|1 the plain run with dynamic generalization in the alternating schedule [default = %d]\n", pPars->fDynRun );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPdr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkDarPdr( Abc_Ntk_t * pNtk, Pdr_Par_t * pPars );
    Pdr_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkUsed, * pNtkFlop = NULL;
    char * pLogFileName = NULL;
    int c;
    Pdr_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MFCDQTHGSLIaxrmuyfqipdegjonctksvwzhb" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRecycle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRecycle < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrameMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfGenLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfGenLimit < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRestLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRestLimit < 0 )
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
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOutOne = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOutOne < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOutGap = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOutGap < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRandomSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRandomSeed < 0 )
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pInvFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'a':
            pPars->fSolveAll ^= 1;
            break;
        case 'x':
            pPars->fStoreCex ^= 1;
            break;
        case 'r':
            pPars->fTwoRounds ^= 1;
            break;
        case 'm':
            pPars->fMonoCnf ^= 1;
            break;
        case 'u':
            pPars->fNewXSim ^= 1;
            break;
        case 'y':
            pPars->fFlopPrio ^= 1;
            break;
        case 'f':
            pPars->fFlopOrder ^= 1;
            break;
        case 'q':
            pPars->fShortest ^= 1;
            break;
        case 'i':
            pPars->fShiftStart ^= 1;
            break;
        case 'p':
            pPars->fReuseProofOblig ^= 1;
            break;
        case 'd':
            pPars->fDumpInv ^= 1;
            break;
        case 'e':
            pPars->fUseSupp ^= 1;
            break;
        case 'g':
            pPars->fSkipGeneral ^= 1;
            break;
        case 'j':
            pPars->fSimpleGeneral ^= 1;
            break;
        case 'o':
            pPars->fUsePropOut ^= 1;
            break;
        case 'n':
            pPars->fSkipDown ^= 1;
            break;
        case 'c':
            pPars->fCtgs ^= 1;
            break;
        case 't':
            pPars->fUseAbs ^= 1;
            break;
        case 'k':
            pPars->fUseSimpleRef ^= 1;
            break;
        case 's':
            pPars->fUseGipSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'z':
            pPars->fNotVerbose ^= 1;
            break;
        case 'b':
            pPars->fBlocking ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -2, "There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -2, "The current network is not an AIG (run \"strash\").\n");
        return 0;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        pNtkFlop = Abc_NtkDup( pNtk );
        Abc_NtkAddLatch( pNtkFlop, Abc_AigConst1(pNtkFlop), ABC_INIT_ONE );
    }
    // run the procedure
    pPars->fUseBridge = pAbc->fBridgeMode;
    pNtkUsed = pNtkFlop ? pNtkFlop : pNtk;
    pAbc->Status  = Abc_NtkDarPdr( pNtkUsed, pPars );
    pAbc->nFrames = pNtkUsed->vSeqModelVec ? -1 : pPars->iFrame;
    Abc_FrameReplacePoStatuses( pAbc, &pPars->vOutMap );
    if ( pNtkUsed->vSeqModelVec )
        Abc_FrameReplaceCexVec( pAbc, &pNtkUsed->vSeqModelVec );
    else
        Abc_FrameReplaceCex( pAbc, &pNtkUsed->pSeqModel );
    if ( pNtkFlop ) Abc_NtkDelete( pNtkFlop );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "pdr" );
    return 0;

usage:
    Abc_Print( -2, "usage: pdr [-MFCDQTHGS <num>] [-LI <file>] [-axrmuyfqipdegjonctksvwzh]\n" );
    Abc_Print( -2, "\t         model checking using property directed reachability (aka IC3)\n" );
    Abc_Print( -2, "\t         pioneered by Aaron R. Bradley (http://theory.stanford.edu/~arbrad/)\n" );
    Abc_Print( -2, "\t         with improvements by Niklas Een (http://een.se/niklas/)\n" );
    Abc_Print( -2, "\t-M num : limit on unused vars to trigger SAT solver recycling [default = %d]\n",       pPars->nRecycle );
    Abc_Print( -2, "\t-F num : limit on timeframes explored to stop computation [default = %d]\n",           pPars->nFrameMax );
    Abc_Print( -2, "\t-C num : limit on conflicts in one SAT call (0 = no limit) [default = %d]\n",          pPars->nConfLimit );
    Abc_Print( -2, "\t-D num : limit on conflicts during ind-generalization (0 = no limit) [default = %d]\n",pPars->nConfGenLimit );
    Abc_Print( -2, "\t-Q num : limit on proof obligations before a restart (0 = no limit) [default = %d]\n", pPars->nRestLimit );
    Abc_Print( -2, "\t-T num : runtime limit, in seconds (0 = no limit) [default = %d]\n",                   pPars->nTimeOut );
    Abc_Print( -2, "\t-H num : runtime limit per output, in milliseconds (with \"-a\") [default = %d]\n",    pPars->nTimeOutOne );
    Abc_Print( -2, "\t-G num : runtime gap since the last CEX (0 = no limit) [default = %d]\n",              pPars->nTimeOutGap );
    Abc_Print( -2, "\t-S num : * value to seed the SAT solver with [default = %d]\n",                          pPars->nRandomSeed );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n",                                          pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-I file: the invariant file name [default = %s]\n",                                    pPars->pInvFileName ? pPars->pInvFileName : "default name" );
    Abc_Print( -2, "\t-a     : toggle solving all outputs even if one of them is SAT [default = %s]\n",      pPars->fSolveAll? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle storing CEXes when solving all outputs [default = %s]\n",              pPars->fStoreCex? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using more effort in generalization [default = %s]\n",                 pPars->fTwoRounds? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using monolythic CNF computation [default = %s]\n",                    pPars->fMonoCnf? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle updated X-valued simulation [default = %s]\n",                         pPars->fNewXSim? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle using structural flop priorities [default = %s]\n",                    pPars->fFlopPrio? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle ordering flops by cost before generalization [default = %s]\n",        pPars->fFlopOrder? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle creating only shortest counter-examples [default = %s]\n",             pPars->fShortest? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle clause pushing from an intermediate timeframe [default = %s]\n",       pPars->fShiftStart? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle reusing proof-obligations in the last timeframe [default = %s]\n",     pPars->fReuseProofOblig? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dumping invariant (valid if init state is all-0) [default = %s]\n",    pPars->fDumpInv? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle using only support variables in the invariant [default = %s]\n",       pPars->fUseSupp? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle skipping expensive generalization step [default = %s]\n",              pPars->fSkipGeneral? "yes": "no" );
    Abc_Print( -2, "\t-j     : toggle using simplified generalization step [default = %s]\n",                pPars->fSimpleGeneral? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using property output as inductive hypothesis [default = %s]\n",       pPars->fUsePropOut? "yes": "no" );
    Abc_Print( -2, "\t-n     : * toggle skipping \'down\' in generalization [default = %s]\n",                 pPars->fSkipDown? "yes": "no" );
    Abc_Print( -2, "\t-c     : * toggle handling CTGs in \'down\' [default = %s]\n",                           pPars->fCtgs? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using abstraction [default = %s]\n",                                   pPars->fUseAbs? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle using simplified refinement [default = %s]\n",                         pPars->fUseSimpleRef? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using the GipSAT solver (ported from rIC3); -f is recommended [default = %s]\n", pPars->fUseGipSat? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n",                       pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing detailed stats default = %s]\n",                              pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle suppressing report about solved outputs [default = %s]\n",             pPars->fNotVerbose? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle clause pushing with blocking [default = %s]\n",                        pPars->fBlocking? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n\n");
    Abc_Print( -2, "\t* Implementation of switches -S, -n, and -c is contributed by Zyad Hassan.\n");
    Abc_Print( -2, "\t  The theory and experiments supporting this work can be found in the following paper:\n");
    Abc_Print( -2, "\t  Zyad Hassan, Aaron R. Bradley, Fabio Somenzi, \"Better Generalization in IC3\", FMCAD 2013.\n");
    Abc_Print( -2, "\t  (http://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD13/papers/85-Better-Generalization-IC3.pdf)\n");



    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BackReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCofTest( Gia_Man_t * pGia, int nFrameMax, int nConfMax, int nTimeMax, int fVerbose );

    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    int nFrameMax = 1000000;
    int nConfMax  = 1000000;
    int nTimeMax  =      10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrameMax < 0 )
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeMax < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9BackReach(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9BackReach(): The number of POs is different from 1.\n" );
        return 1;
    }
    pTemp = Gia_ManCofTest( pAbc->pGia, nFrameMax, nConfMax, nTimeMax, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &back_reach [-FCT <num>] [-vh]\n" );
    Abc_Print( -2, "\t         performs backward reachability by circuit cofactoring\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", nFrameMax );
    Abc_Print( -2, "\t-C num : the conflict limit at a node during induction [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-T num : the timeout for property directed reachability [default = %d]\n", nTimeMax );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

#ifdef ABC_USE_CUDD
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachM( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Gia_ParLlb_t Pars, * pPars = &Pars;
    char * pLogFileName = NULL;
    int c;
    extern int Llb_ManModelCheckGia( Gia_Man_t * pGia, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TBFCHSLripcsyzvwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nClusterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nClusterMax < 0 )
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nHintDepth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nHintDepth < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->HintFirst = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->HintFirst < 0 )
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
            pPars->fReorder ^= 1;
            break;
        case 'i':
            pPars->fIndConstr ^= 1;
            break;
        case 'p':
            pPars->fUsePivots ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 's':
            pPars->fSchedule ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pAbc->Status  = Llb_ManModelCheckGia( pAbc->pGia, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachm" );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachm [-TBFCHS num] [-L file] [-ripcsyzvwh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (dependence-matrix-based)\n" );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-B num : max number of nodes in the intermediate BDDs [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-C num : max number of variables in a cluster [default = %d]\n", pPars->nClusterMax );
    Abc_Print( -2, "\t-H num : max number of hints to use [default = %d]\n", pPars->nHintDepth );
    Abc_Print( -2, "\t-S num : the number of the starting hint [default = %d]\n", pPars->HintFirst );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s]\n", pPars->fReorder? "yes": "no" );
    Abc_Print( -2, "\t-i     : enable extraction of inductive constraints [default = %s]\n", pPars->fIndConstr? "yes": "no" );
    Abc_Print( -2, "\t-p     : enable partitions for internal cut-points [default = %s]\n", pPars->fUsePivots? "yes": "no" );
    Abc_Print( -2, "\t-c     : enable clustering of partitions [default = %s]\n", pPars->fCluster? "yes": "no" );
    Abc_Print( -2, "\t-s     : enable scheduling of clusters [default = %s]\n", pPars->fSchedule? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : prints dependency matrix [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
#endif

#ifdef ABC_USE_CUDD
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachP( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;
    extern int Llb_ManReachMinCut( Aig_Man_t * pAig, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NBFTLrbyzdvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartValue = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartValue < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 )
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
            pPars->fReorder ^= 1;
            break;
        case 'b':
            pPars->fBackward ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
            break;
        case 'd':
            pPars->fDumpReached ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_ManReachMinCut( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachp" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachp [-NFT num] [-L file] [-rbyzdvwh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (partitioning-based)\n" );
    Abc_Print( -2, "\t-N num : partitioning value (MinVol=nANDs/N/2; MaxVol=nANDs/N) [default = %d]\n", pPars->nPartValue );
//    Abc_Print( -2, "\t-B num : the BDD node increase when hints kick in [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );
    Abc_Print( -2, "\t-b     : perform backward reachability analysis [default = %s]\n", pPars->fBackward? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );
    Abc_Print( -2, "\t-d     : dump BDD of reached states into file \"reached.blif\" [default = %s]\n", pPars->fDumpReached? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
#endif

#ifdef ABC_USE_CUDD
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachN( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;
    extern int Llb_NonlinCoreReach( Aig_Man_t * pAig, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BFTLryzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 )
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
            pPars->fReorder ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_NonlinCoreReach( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachn" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachn [-BFT num] [-L file] [-ryzvh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (non-linear-QS-based)\n" );
    Abc_Print( -2, "\t-B num : the BDD node increase when hints kick in [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
#endif

#ifdef ABC_USE_CUDD
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachY( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    pPars->fCluster = 0;
    pPars->fReorder = 0;
    pPars->nBddMax     = 100;
    pPars->nClusterMax = 500;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BCFTLbcryzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nClusterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nClusterMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 )
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'b':
            pPars->fBackward ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): The current AIG has no latches.\n" );
        return 0;
    }
//    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
//    {
//        Abc_Print( -1, "Abc_CommandAbc9ReachN(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
//        return 0;
//    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_Nonlin4CoreReach( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachy" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachy [-BCFT num] [-L file] [-bcryzvh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (non-linear-QS-based)\n" );
    Abc_Print( -2, "\t-B num : the max BDD size to introduce cut points [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-C num : the max BDD size to reparameterize/cluster [default = %d]\n", pPars->nClusterMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-b     : enable using backward enumeration [default = %s]\n", pPars->fBackward? "yes": "no" );
    Abc_Print( -2, "\t-c     : enable reparametrization clustering [default = %s]\n", pPars->fCluster? "yes": "no" );
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
#endif

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GroupProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Gia_ManGroupProve( Gia_Man_t * p, char * pCommLine, int nGroupSize, int fVerbose );
    Vec_Int_t * vStatus;
    char * pCommLine = NULL;
    int c, nGroupSize = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "GSvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nGroupSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nGroupSize <= 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a file name.\n" );
                goto usage;
            }
            pCommLine = argv[globalUtilOptind];
            globalUtilOptind++;
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
        Abc_Print( -1, "Abc_CommandAbc9GroupProve(): There is no AIG.\n" );
        return 1;
    }
    if ( pCommLine == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GroupProve(): Command line is not given.\n" );
        return 1;
    }
    vStatus = Gia_ManGroupProve( pAbc->pGia, pCommLine, nGroupSize, fVerbose );
    Vec_IntFree( vStatus );
    return 0;

usage:
    Abc_Print( -2, "usage: &gprove [-GS num] [-vh]\n" );
    Abc_Print( -2, "\t         proves multi-output testcase by splitting outputs into groups\n" );
    Abc_Print( -2, "\t         (currently, group size more than one works only for \"bmc3\" and \"pdr\")\n" );
    Abc_Print( -2, "\t-G num : the size of one group [default = %d]\n", nGroupSize );
    Abc_Print( -2, "\t-S str : the command line to be executed for each group [default = %s]\n", pCommLine ? pCommLine : "none" );
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
int Abc_CommandAbc9MultiProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManMultiProve( Gia_Man_t * p, Bmc_MulPar_t * pPars );
    Vec_Int_t * vStatuses; int c;
    Bmc_MulPar_t Pars, * pPars = &Pars;
    memset( pPars, 0, sizeof(Bmc_MulPar_t) );
    pPars->TimeOutGlo =  30;
    pPars->TimeOutLoc =   2;
    pPars->TimeOutInc = 100;
    pPars->TimeOutGap =   0;
    pPars->TimePerOut =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TLMGHsdvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOutGlo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOutGlo < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOutLoc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOutLoc <= 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeOutInc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeOutInc <= 0 )
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
            if ( pPars->TimeOutGap <= 0 )
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimePerOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimePerOut <= 0 )
                goto usage;
            break;
        case 's':
            pPars->fUseSyn ^= 1;
            break;
        case 'd':
            pPars->fDumpFinal ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9MultiProve(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9MultiProve(): The problem is combinational.\n" );
        return 1;
    }
    pAbc->Status = Gia_ManMultiProve( pAbc->pGia, pPars );
    vStatuses = Abc_FrameDeriveStatusArray( pAbc->pGia->vSeqModelVec );
    Abc_FrameReplacePoStatuses( pAbc, &vStatuses );
    Abc_FrameReplaceCexVec( pAbc, &pAbc->pGia->vSeqModelVec );
    return 0;

usage:
    Abc_Print( -2, "usage: &mprove [-TLMGH num] [-sdvwh]\n" );
    Abc_Print( -2, "\t         proves multi-output testcase by applying several engines\n" );
    Abc_Print( -2, "\t-T num : approximate global runtime limit in seconds [default = %d]\n",     pPars->TimeOutGlo );
    Abc_Print( -2, "\t-L num : approximate local runtime limit in seconds [default = %d]\n",      pPars->TimeOutLoc );
    Abc_Print( -2, "\t-M num : percentage of local runtime limit increase [default = %d]\n",      pPars->TimeOutInc );
    Abc_Print( -2, "\t-G num : approximate gap runtime limit in seconds [default = %d]\n",        pPars->TimeOutGap );
    Abc_Print( -2, "\t-H num : timeout per output in milliseconds [default = %d]\n",              pPars->TimePerOut );
    Abc_Print( -2, "\t-s     : toggle using combinational synthesis [default = %s]\n",            pPars->fUseSyn?      "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dumping invariant into a file [default = %s]\n",            pPars->fDumpFinal?   "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",             pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing additional verbose information [default = %s]\n",  pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pGiaUse = pAbc->pGia, * pGiaTemp = NULL;
    Wlc_Ntk_t * pWlc = (Wlc_Ntk_t *)pAbc->pAbcWlc;
    char * pReplayFile = NULL, * pUfarArgs = NULL, * pUfarArgsAlloc = NULL;
    int c, nProcs = 6, nProcsNew = 0, nTimeOut = 3, nTimeOut2 = 10, nTimeOut3 = 100, fUseUif = 0, fVerbose = 0, fVeryVerbose = 0, fSilent = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PTUCWRusvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nProcsNew = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProcsNew <= 0 || nProcsNew > 6 )
                goto usage;
            nProcs = nProcsNew;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut <= 0 )
                goto usage;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeOut2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut2 <= 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a string.\n" );
                goto usage;
            }
            {
                int iArg, nChars = 0;
                ABC_FREE( pUfarArgsAlloc );
                for ( iArg = globalUtilOptind; iArg < argc; iArg++ )
                    nChars += (int)strlen(argv[iArg]) + 1;
                pUfarArgsAlloc = ABC_ALLOC( char, nChars + 1 );
                pUfarArgsAlloc[0] = 0;
                for ( iArg = globalUtilOptind; iArg < argc; iArg++ )
                {
                    if ( iArg > globalUtilOptind )
                        strcat( pUfarArgsAlloc, " " );
                    strcat( pUfarArgsAlloc, argv[iArg] );
                }
                pUfarArgs = pUfarArgsAlloc;
                globalUtilOptind = argc;
            }
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeOut3 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut3 <= 0 )
                goto usage;
            break;                          
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by a file name.\n" );
                goto usage;
            }
            pReplayFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'u':
            fUseUif ^= 1;
            break;
        case 's':
            fSilent ^= 1;
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
    if ( fUseUif )
    {
        pGiaUse = NULL;
        if ( pWlc == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve(): There is no word-level design for option \"-u\".\n" );
            ABC_FREE( pUfarArgsAlloc );
            return 1;
        }
        pGiaTemp = Wlc_NtkBitBlast( pWlc, NULL );
        if ( pGiaTemp == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve(): Word-level bit-blasting has failed.\n" );
            ABC_FREE( pUfarArgsAlloc );
            return 1;
        }
        if ( (Gia_ManPoNum(pGiaTemp) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve(): Internal \"&miter -x\" requires even number of bit-level outputs.\n" );
            Gia_ManStop( pGiaTemp );
            ABC_FREE( pUfarArgsAlloc );
            return 1;
        }
        pGiaUse = Gia_ManTransformMiter2( pGiaTemp );
        Gia_ManStop( pGiaTemp );
        pGiaTemp = NULL;
    }
    else if ( pUfarArgs != NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve(): Option \"-C\" requires \"-u\".\n" );
        ABC_FREE( pUfarArgsAlloc );
        return 1;
    }
    if ( pGiaUse == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve(): There is no AIG.\n" );
        ABC_FREE( pUfarArgsAlloc );
        return 1;
    }
    if ( Gia_ManRegNum(pGiaUse) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve(): The problem is combinational.\n" );
        if ( fUseUif )
            Gia_ManStop( pGiaUse );
        ABC_FREE( pUfarArgsAlloc );
        return 1;
    }
    pAbc->Status = Cec_GiaProveTest( pGiaUse, nProcs, nTimeOut, nTimeOut2, nTimeOut3, fUseUif, pWlc, fVerbose, fVeryVerbose, fSilent, pReplayFile, pUfarArgs );
    Abc_FrameReplaceCex( pAbc, &pGiaUse->pCexSeq ); 
    if ( fUseUif )
        Gia_ManStop( pGiaUse );
    ABC_FREE( pUfarArgsAlloc );
    return 0;

usage:
    Abc_Print( -2, "usage: &sprove [-PTUW num] [-C str] [-R file] [-usvwh]\n" );
    Abc_Print( -2, "\t         concurrent sequential model checker\n" );
    Abc_Print( -2, "\t-P num : the number of concurrent processes (1 <= num <= 6) [default = %d]\n", nProcs );
    Abc_Print( -2, "\t-T num : first-stage timeout for proving original and scnew reduction [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-U num : second-stage proving timeout on optimized miter [default = %d]\n", nTimeOut2 );
    Abc_Print( -2, "\t-W num : late-stage timeout for optimization and final proving [default = %d]\n", nTimeOut3 );
    Abc_Print( -2, "\t-C str : with -u, pass this option string to internal %%ufar\n" );
    Abc_Print( -2, "\t-R str : dump replay/trace file for later execution by &sprove2\n" );
    Abc_Print( -2, "\t-u     : enable concurrent UFAR on word-level design (uses internal %%blast + &miter -x)\n" );
    Abc_Print( -2, "\t-s     : enable silent computation (no reporting) [default = %s]\n",    fSilent? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",         fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing more verbose information [default = %s]\n",    fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    ABC_FREE( pUfarArgsAlloc );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SProve2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pGiaUse = pAbc->pGia, * pGiaTemp = NULL;
    Wlc_Ntk_t * pWlc = (Wlc_Ntk_t *)pAbc->pAbcWlc;
    char * pTraceFile = NULL;
    int c, nProcs = 0, nTimeOut = 0, nTimeOut2 = 0, nTimeOut3 = 0, fUseUif = 0, fVerbose = 0, fVeryVerbose = 0, fSilent = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSilent ^= 1;
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
    if ( globalUtilOptind >= argc )
    {
        Abc_Print( -1, "Command &sprove2 expects a replay file name.\n" );
        goto usage;
    }
    pTraceFile = argv[globalUtilOptind];
    globalUtilOptind++;
    if ( globalUtilOptind != argc )
        goto usage;
    if ( !Cec_GiaReplayReadParams( pTraceFile, &nProcs, &nTimeOut, &nTimeOut2, &nTimeOut3, &fUseUif ) )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve2(): Cannot read replay file \"%s\".\n", pTraceFile );
        return 1;
    }
    if ( fUseUif )
    {
        pGiaUse = NULL;
        if ( pWlc == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve2(): Replay requires word-level design for UIF mode.\n" );
            return 1;
        }
        pGiaTemp = Wlc_NtkBitBlast( pWlc, NULL );
        if ( pGiaTemp == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve2(): Word-level bit-blasting has failed.\n" );
            return 1;
        }
        if ( (Gia_ManPoNum(pGiaTemp) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandAbc9SProve2(): Internal \"&miter -x\" requires even number of bit-level outputs.\n" );
            Gia_ManStop( pGiaTemp );
            return 1;
        }
        pGiaUse = Gia_ManTransformMiter2( pGiaTemp );
        Gia_ManStop( pGiaTemp );
        pGiaTemp = NULL;
    }
    if ( pGiaUse == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve2(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pGiaUse) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9SProve2(): The problem is combinational.\n" );
        if ( fUseUif )
            Gia_ManStop( pGiaUse );
        return 1;
    }
    pAbc->Status = Cec_GiaReplayTest( pGiaUse, pWlc, pTraceFile, fVerbose, fVeryVerbose, fSilent );
    Abc_FrameReplaceCex( pAbc, &pGiaUse->pCexSeq );
    if ( fUseUif )
        Gia_ManStop( pGiaUse );
    return 0;

usage:
    Abc_Print( -2, "usage: &sprove2 <trace_file> [-svwh]\n" );
    Abc_Print( -2, "\t         replays &sprove strategy stored in the given trace file\n" );
    Abc_Print( -2, "\t-s     : enable silent computation (no reporting) [default = %s]\n",    fSilent? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",         fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing more verbose information [default = %s]\n",    fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Bmc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Bmc_AndPar_t Pars, * pPars = &Pars;
    memset( pPars, 0, sizeof(Bmc_AndPar_t) );
    pPars->nStart        =    0;  // starting timeframe
    pPars->nFramesMax    =    0;  // maximum number of timeframes
    pPars->nFramesAdd    =   50;  // the number of additional frames
    pPars->nConfLimit    =    0;  // maximum number of conflicts at a node
    pPars->nTimeOut      =    0;  // timeout in seconds
    pPars->nLutSize      =    6;  // max LUT size for CNF computation
    pPars->nProcs        =    1;  // the number of parallel solvers
    pPars->fLoadCnf      =    0;  // dynamic CNF loading
    pPars->fDumpFrames   =    0;  // dump unrolled timeframes
    pPars->fUseSynth     =    0;  // use synthesis
    pPars->fUseOldCnf    =    0;  // use old CNF construction
    pPars->fVerbose      =    0;  // verbose
    pPars->fVeryVerbose  =    0;  // very verbose
    pPars->fNotVerbose   =    0;  // skip line-by-line print-out
    pPars->iFrame        =    0;  // explored up to this frame
    pPars->nFailOuts     =    0;  // the number of failed outputs
    pPars->nDropOuts     =    0;  // the number of dropped outputs
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFATKdscvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesAdd < 0 )
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
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 0 )
                goto usage;
            break;
        case 'd':
            pPars->fDumpFrames ^= 1;
            break;
        case 's':
            pPars->fUseSynth ^= 1;
            break;
        case 'c':
            pPars->fUseOldCnf ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmc(): There is no AIG.\n" );
        return 0;
    }
    pAbc->Status  = Gia_ManBmcPerform( pAbc->pGia, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &bmc [-SFATK num] [-dscvwh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking\n" );
    Abc_Print( -2, "\t-S num : the starting timeframe [default = %d]\n",                      pPars->nStart );
    Abc_Print( -2, "\t-F num : the maximum number of timeframes [default = %d]\n",            pPars->nFramesMax );
    Abc_Print( -2, "\t-A num : the number of additional frames to unroll [default = %d]\n",   pPars->nFramesAdd );
    Abc_Print( -2, "\t-T num : approximate timeout in seconds [default = %d]\n",              pPars->nTimeOut );
    Abc_Print( -2, "\t-K num : the maximum cut size for CNF computation [default = %d]\n",    pPars->nLutSize );
    Abc_Print( -2, "\t-d     : toggle dumping unfolded timeframes [default = %s]\n",          pPars->fDumpFrames?  "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle synthesizing unrolled timeframes [default = %s]\n",     pPars->fUseSynth?    "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using old CNF computation [default = %s]\n",            pPars->fUseOldCnf?   "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",         pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing information about unfolding [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SBmc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Bmcs_ManPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars );
    extern int Bmcg_ManPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars );
    Bmc_AndPar_t Pars, * pPars = &Pars; int c;
    memset( pPars, 0, sizeof(Bmc_AndPar_t) );
    pPars->nStart        =    0;  // starting timeframe
    pPars->nFramesMax    =    0;  // maximum number of timeframes
    pPars->nFramesAdd    =    1;  // the number of additional frames
    pPars->nConfLimit    =    0;  // maximum number of conflicts at a node
    pPars->nTimeOut      =    0;  // timeout in seconds
    pPars->nLutSize      =    0;  // max LUT size for CNF computation
    pPars->nProcs        =    1;  // the number of parallel solvers
    pPars->fLoadCnf      =    0;  // dynamic CNF loading
    pPars->fDumpFrames   =    0;  // dump unrolled timeframes
    pPars->fUseSynth     =    0;  // use synthesis
    pPars->fUseOldCnf    =    0;  // use old CNF construction
    pPars->fUseGlucose   =    0;  // use Glucose 3.0
    pPars->fUseEliminate =    0;  // use variable elimination
    pPars->fVerbose      =    0;  // verbose
    pPars->fVeryVerbose  =    0;  // very verbose
    pPars->fNotVerbose   =    0;  // skip line-by-line print-out
    pPars->iFrame        =    0;  // explored up to this frame
    pPars->nFailOuts     =    0;  // the number of failed outputs
    pPars->nDropOuts     =    0;  // the number of dropped outputs
    pPars->pFuncOnFrameDone = pAbc->pFuncOnFrameDone; // frame done callback

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PCFATgevwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesAdd < 0 )
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
        case 'g':
            pPars->fUseGlucose ^= 1;
            break;
        case 'e':
            pPars->fUseEliminate ^= 1;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmcs(): There is no AIG.\n" );
        return 0;
    }
    if ( pPars->nProcs > 4 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmcs(): Currently this command can run at most 4 concurrent solvers.\n" );
        return 0;
    }
    pAbc->Status  = pPars->fUseGlucose ? Bmcg_ManPerform(pAbc->pGia, pPars) : Bmcs_ManPerform(pAbc->pGia, pPars);
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &bmcs [-PCFAT num] [-gevwh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking\n" );
    Abc_Print( -2, "\t-P num : the number of parallel solvers [default = %d]\n",              pPars->nProcs );
    Abc_Print( -2, "\t-C num : the SAT solver conflict limit [default = %d]\n",               pPars->nConfLimit );
    Abc_Print( -2, "\t-F num : the maximum number of timeframes [default = %d]\n",            pPars->nFramesMax );
    Abc_Print( -2, "\t-A num : the number of additional frames to unroll [default = %d]\n",   pPars->nFramesAdd );
    Abc_Print( -2, "\t-T num : approximate timeout in seconds [default = %d]\n",              pPars->nTimeOut );
    Abc_Print( -2, "\t-g     : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", pPars->fUseGlucose?  "Glucose" : "Satoko" );
    Abc_Print( -2, "\t-e     : toggle using variable eliminatation [default = %s]\n",         pPars->fUseEliminate?"yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",         pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing information about unfolding [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ChainBmc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Bmc_ChainTest( Gia_Man_t * p, int nFrameMax, int nConfMax, int fVerbose, int fVeryVerbose, Vec_Ptr_t ** pvCexes );
    Vec_Ptr_t * vCexes = NULL;
    int nFrameMax    =  200;
    int nConfMax     =    0;
    int fVerbose     =    0;
    int fVeryVerbose =    0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrameMax < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9ChainBmc(): There is no AIG.\n" );
        return 0;
    }
    if ( !Gia_ManRegNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ChainBmc(): The AIG is combinational.\n" );
        return 0;
    }
    Bmc_ChainTest( pAbc->pGia, nFrameMax, nConfMax, fVerbose, fVeryVerbose, &vCexes );
    if ( vCexes ) Vec_PtrFreeFree( vCexes );
    //pAbc->Status  = ...;
    //pAbc->nFrames = pPars->iFrame;
    //Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;
usage:
    Abc_Print( -2, "usage: &chainbmc [-FC <num>] [-vwh]\n" );
    Abc_Print( -2, "\t           runs a specialized flavor of BMC\n" );
    Abc_Print( -2, "\t-F <num> : the max number of timeframes (0 = unused) [default = %d]\n", nFrameMax );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts (0 = unused) [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing even more information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BCore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Bmc_BCorePar_t Pars, * pPars = &Pars;
    memset( pPars, 0, sizeof(Bmc_BCorePar_t) );
    pPars->iFrame        =   10;  // timeframe
    pPars->iOutput       =    0;  // property output
    pPars->nTimeOut      =    0;  // timeout in seconds
    pPars->pFilePivots   = NULL;  // file name with AIG IDs of pivot objects
    pPars->pFileProof    = NULL;  // file name to write the resulting proof
    pPars->fVerbose      =    0;  // verbose output
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FOTVvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->iFrame = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->iFrame < 0 )
                goto usage;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->iOutput < 0 )
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
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pFilePivots = argv[globalUtilOptind];
            globalUtilOptind++;
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
        Abc_Print( -1, "Abc_CommandAbc9BCore(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9BCore(): AIG has no registers.\n" );
        return 0;
    }
    // get the file name
    if ( pPars->pFilePivots != NULL )
    {
        FILE * pFile;
        pFile = fopen( pPars->pFilePivots, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9BCore(): Cannot open file \"%s\" with pivot node IDs.\n", pPars->pFilePivots );
            return 0;
        }
        fclose( pFile );
    }
    // get the file name
    if ( argc == globalUtilOptind + 1 )
    {
        FILE * pFile;
        pPars->pFileProof = argv[globalUtilOptind];
        pFile = fopen( pPars->pFileProof, "wb" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9BCore(): Cannot open file \"%s\" for writing the proof.\n", pPars->pFileProof );
            return 0;
        }
        fclose( pFile );
    }
    Bmc_ManBCorePerform( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &bcore [-FOTV num] [-vh] <file>\n" );
    Abc_Print( -2, "\t         records UNSAT core of the BMC instance\n" );
    Abc_Print( -2, "\t-F num : the zero-based index of a timeframe [default = %d]\n",         pPars->iFrame );
    Abc_Print( -2, "\t-O num : the zero-based index of a primary output [default = %d]\n",    pPars->iOutput );
    Abc_Print( -2, "\t-T num : approximate timeout in seconds [default = %d]\n",              pPars->nTimeOut );
    Abc_Print( -2, "\t-V file: file name with AIG IDs of pivot variables [default = no pivots]\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",         pPars->fVerbose?     "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name to write the resulting proof [default = stdout]\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ICheck( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, nFramesMax = 1, nTimeOut = 0, fEmpty = 0, fSearch = 1, fReverse = 0, fBackTopo = 0, fDump = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MTesrbdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesMax <= 0 )
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
        case 'e':
            fEmpty ^= 1;
            break;
        case 's':
            fSearch ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;
        case 'b':
            fBackTopo ^= 1;
            break;
        case 'd':
            fDump ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9ICheck(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ICheck(): The AIG is combinational.\n" );
        return 0;
    }
    Vec_IntFreeP( &pAbc->vIndFlops );
    if ( fSearch )
        pAbc->vIndFlops = Bmc_PerformISearch( pAbc->pGia, nFramesMax, nTimeOut, fReverse, fBackTopo, fDump, fVerbose );
    else
        Bmc_PerformICheck( pAbc->pGia, nFramesMax, nTimeOut, fEmpty, fVerbose );
    pAbc->nIndFrames = pAbc->vIndFlops ? nFramesMax : 0;
    return 0;

usage:
    Abc_Print( -2, "usage: &icheck [-MT num] [-esrbdvh]\n" );
    Abc_Print( -2, "\t         performs specialized induction check\n" );
    Abc_Print( -2, "\t-M num : the number of timeframes used for induction [default = %d]\n",    nFramesMax );
    Abc_Print( -2, "\t-T num : approximate global runtime limit in seconds [default = %d]\n",    nTimeOut );
    Abc_Print( -2, "\t-e     : toggle using empty set of next-state functions [default = %s]\n", fEmpty? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle searching for a minimal subset [default = %s]\n",          fSearch? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle searching in the reverse order [default = %s]\n",          fReverse? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle searching in backward order from POs [default = %s]\n",    fBackTopo? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle printing out the resulting set [default = %s]\n",          fDump? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",            fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Bmci( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManBmciTest( Gia_Man_t * p, Vec_Int_t * vInit, int nFrames, int nWords, int nTimeOut, int fSim, int fVerbose );
    int c, nFrames = 1000, nWords = 1000, nTimeOut = 0, fSim = 0, fVerbose = 0;
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
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): AIG is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vInitClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bmci(): Init array is not given.\n" );
        return 0;
    }
    Gia_ManBmciTest( pAbc->pGia, pAbc->pGia->vInitClasses, nFrames, nWords, nTimeOut, fSim, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &bmci [-FWT num] [-svh]\n" );
    Abc_Print( -2, "\t         experimental procedure\n" );
    Abc_Print( -2, "\t-F num : the number of timeframes [default = %d]\n",                    nFrames );
    Abc_Print( -2, "\t-W num : the number of machine words [default = %d]\n",                 nWords );
    Abc_Print( -2, "\t-T num : approximate global runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-s     : toggles using ternary simulation [default = %s]\n",            fSim?     "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",        fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
