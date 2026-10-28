/**CFile****************************************************************

  FileName    [abcRewrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Combinational rewriting.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "opt/dar/dar.h"
#include "opt/drw/drw.h"
#include "bool/kit/kit.h"
#include "opt/cut/cut.h"
#include <errno.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandBalance                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxStruct              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCleanup                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSweep                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRmInverter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRewrite                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRefactor               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRestructure            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRr                     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrchestrate            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAIGAugmentation       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewrite               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRewrite               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRefactor              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDc2                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDrwsat                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIResyn                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandHaig                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRewire                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9RexWalk            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resyn3             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resyn3rs           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Compress3rs        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dc2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dc3                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Shrink             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Balance            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BalanceLut         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Reshape            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Syn2               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Syn3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Syn4               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Drw                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Drf                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LNetOpt            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Ttopt              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Transduction       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9TranStoch          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Rrr                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Rewire             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9DeepSyn            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9RandSyn            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatSyn             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9StochSyn           ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers combinational rewriting commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitRewrite( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "b",             Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "balance",       Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mux_struct",    Abc_CommandMuxStruct,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cleanup",       Abc_CommandCleanup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "sweep",         Abc_CommandSweep,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "rewrite",       Abc_CommandRewrite,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "refactor",      Abc_CommandRefactor,         1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "restructure",   Abc_CommandRestructure,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "rd_inv",        Abc_CommandRmInverter,       1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "rr",            Abc_CommandRr,               1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "orchestrate",  Abc_CommandOrchestrate,       1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "aigaug",       Abc_CommandAIGAugmentation,   1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irw",           Abc_CommandIRewrite,         1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drw",           Abc_CommandDRewrite,         1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drf",           Abc_CommandDRefactor,        1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dc2",           Abc_CommandDc2,              1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drwsat",        Abc_CommandDrwsat,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "iresyn",        Abc_CommandIResyn,           1 );
//    Cmd_CommandAdd( pAbc, "New AIG",      "haig",          Abc_CommandHaig,             1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "rewire",        Abc_CommandRewire,           1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&rexwalk",      Abc_CommandAbc9RexWalk,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resyn3",       Abc_CommandAbc9Resyn3,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resyn3rs",     Abc_CommandAbc9Resyn3rs,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&compress3rs",  Abc_CommandAbc9Compress3rs,  0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dc2",          Abc_CommandAbc9Dc2,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dc3",          Abc_CommandAbc9Dc3,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&shrink",       Abc_CommandAbc9Shrink,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&b",            Abc_CommandAbc9Balance,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&blut",         Abc_CommandAbc9BalanceLut,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reshape",      Abc_CommandAbc9Reshape,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&syn2",         Abc_CommandAbc9Syn2,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&syn3",         Abc_CommandAbc9Syn3,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&syn4",         Abc_CommandAbc9Syn4,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&drw",          Abc_CommandAbc9Drw,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&drf",          Abc_CommandAbc9Drf,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lnetopt",      Abc_CommandAbc9LNetOpt,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&ttopt",        Abc_CommandAbc9Ttopt,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&transduction", Abc_CommandAbc9Transduction, 0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&transtoch"   , Abc_CommandAbc9TranStoch,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&rrr",          Abc_CommandAbc9Rrr,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&rewire"      , Abc_CommandAbc9Rewire,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&deepsyn",      Abc_CommandAbc9DeepSyn,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&randsyn",      Abc_CommandAbc9RandSyn,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&satsyn",       Abc_CommandAbc9SatSyn,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&stochsyn",     Abc_CommandAbc9StochSyn,     0 );
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
int Abc_CommandBalance( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    int fDuplicate;
    int fSelective;
    int fUpdateLevel;
    int fExor;
    int fVerbose;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fDuplicate   = 0;
    fSelective   = 0;
    fUpdateLevel = 1;
    fExor        = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ldsxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'd':
            fDuplicate ^= 1;
            break;
        case 's':
            fSelective ^= 1;
            break;
        case 'x':
            fExor ^= 1;
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
    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( fExor )
            pNtkRes = Abc_NtkBalanceExor( pNtk, fUpdateLevel, fVerbose );
        else
            pNtkRes = Abc_NtkBalance( pNtk, fDuplicate, fSelective, fUpdateLevel );
    }
    else
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtkTemp == NULL )
        {
            Abc_Print( -1, "Strashing before balancing has failed.\n" );
            return 1;
        }
        if ( fExor )
            pNtkRes = Abc_NtkBalanceExor( pNtkTemp, fUpdateLevel, fVerbose );
        else
            pNtkRes = Abc_NtkBalance( pNtkTemp, fDuplicate, fSelective, fUpdateLevel );
        Abc_NtkDelete( pNtkTemp );
    }

    // check if balancing worked
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Balancing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: balance [-ldsxvh]\n" );
    Abc_Print( -2, "\t        transforms the current network into a well-balanced AIG\n" );
    Abc_Print( -2, "\t-l    : toggle minimizing the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-s    : toggle duplication on the critical paths [default = %s]\n", fSelective? "yes": "no" );
    Abc_Print( -2, "\t-x    : toggle balancing multi-input EXORs [default = %s]\n", fExor? "yes": "no" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMuxStruct( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkMuxRestructure( Abc_Ntk_t * pNtk, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fVerbose     = 0;
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
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Does not work for a logic network.\n" );
        return 1;
    }
    // check if balancing worked
//    pNtkRes = Abc_NtkMuxRestructure( pNtk, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "MUX restructuring has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: mux_struct [-vh]\n" );
    Abc_Print( -2, "\t        performs MUX restructuring of the current network\n" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCleanup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fCleanupPis;
    int fCleanupPos;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarCleanupAig( Abc_Ntk_t * pNtk, int fCleanupPis, int fCleanupPos, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fCleanupPis = 1;
    fCleanupPos = 1;
    fVerbose    = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "iovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fCleanupPis ^= 1;
            break;
        case 'o':
            fCleanupPos ^= 1;
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
    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( !fCleanupPis && !fCleanupPos )
        {
            Abc_Print( -1, "Cleanup for PIs and POs is not enabled.\n" );
            pNtkRes = Abc_NtkDup( pNtk );
        }
        else
            pNtkRes = Abc_NtkDarCleanupAig( pNtk, fCleanupPis, fCleanupPos, fVerbose );
    }
    else
    {
        Abc_NtkCleanup( pNtk, fVerbose );
        pNtkRes = Abc_NtkDup( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cleanup [-iovh]\n" );
    Abc_Print( -2, "\t        for logic networks, removes dangling combinatinal logic\n" );
    Abc_Print( -2, "\t        for AIGs, removes PIs w/o fanout and POs driven by const-0\n" );
    Abc_Print( -2, "\t-i    : toggles removing PIs without fanout [default = %s]\n", fCleanupPis? "yes": "no" );
    Abc_Print( -2, "\t-o    : toggles removing POs with const-0 drivers [default = %s]\n", fCleanupPos? "yes": "no" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fSingle = 0;
    int fVerbose = 0;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSingle ^= 1;
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
        Abc_Print( -1, "The classical (SIS-like) sweep can only be performed on a logic network.\n" );
        return 1;
    }
    // modify the current network
    if ( fSingle )
        Abc_NtkSweepBufsInvs( pNtk, fVerbose );
    else
        Abc_NtkSweep( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: sweep [-svh]\n" );
    Abc_Print( -2, "\t        removes dangling nodes; propagates constant, buffers, inverters\n" );
    Abc_Print( -2, "\t-s    : toggle sweeping buffers/inverters only [default = %s]\n", fSingle? "yes": "no" );
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
int Abc_CommandRmInverter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Extra_UtilGetoptReset();
    int iVerbose = 0;
    int c;
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            iVerbose ^= 1;
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
    if ( !Abc_NtkHasAig(pNtk) || !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command only works on AIG network.\n" );
        return 1;
    }
    Abc_NtkRmInverter(pNtk, iVerbose);
    return 0;

usage:
    Abc_Print( -2, "usage: rd_inv\n" );
    Abc_Print( -2, "\t            redistribute inverters on self-dual and self-anti-dual functions in network\n" );
    Abc_Print( -2, "\t-v        : verbose output\n");
    Abc_Print( -2, "\t-h        : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOrchestrate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;

    int nNodeSizeMax;
    int nConeSizeMax;
    int fUpdateLevel;
    int fUseZeros_rwr;
    int fUseZeros_ref;
    int fUseDcs;
    int RS_CUT_MIN =  4;//rs option
    int RS_CUT_MAX = 16;//rs option
    int nCutsMax; //rs option
    int nNodesMax; //rs option
    int nLevelsOdc; //rs option

    int fPrecompute; //rewrite option (not enabled)
    int fPlaceEnable; //rewrite option (not enabled)

    int fVerbose; //rewrite/rs/rf verbose
    int fVeryVerbose; //very verbose option for all 
    //size_t NtkSize;
    extern void Rwr_Precompute();

    //local greedy
    extern int Abc_NtkOrchLocal( Abc_Ntk_t * pNtk, int fUseZeros_rwr, int fUseZeros_ref, int fPlaceEnable, int nCutsMax, int nNodesMax, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int nNodeSizeMax, int nConeSizeMax, int fUseDcs );
    //priority orch
    extern int Abc_NtkOchestration( Abc_Ntk_t * pNtk, Vec_Int_t **pGain_rwr, Vec_Int_t **pGain_res,Vec_Int_t **pGain_ref, int sOpsOrder, int fUseZeros_rwr, int fUseZeros_ref, int fPlaceEnable, int nCutsMax, int nNodesMax, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int nNodeSizeMax, int nConeSizeMax, int fUseDcs );
    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros_rwr =  1;
    fUseZeros_ref =  1;
    fUseDcs      =  0;
    fVerbose     =  0;
    fVeryVerbose = 0;
    fPlaceEnable = 0;
    fPrecompute  = 0;
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNFZzlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 )
                goto usage;
            break;
       case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodesMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelsOdc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelsOdc < 0 )
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros_rwr ^= 1;
            break;
        case 'Z':
            fUseZeros_ref ^= 1;
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
        }
    }
    if ( fPrecompute )
    {
        Rwr_Precompute();
        return 0;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < RS_CUT_MIN || nCutsMax > RS_CUT_MAX )
    {
        Abc_Print( -1, "Can only compute cuts for %d <= K <= %d.\n", RS_CUT_MIN, RS_CUT_MAX );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }
    if ( nNodeSizeMax > 15 )
    {
        Abc_Print( -1, "The cone size cannot exceed 15.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        Abc_Print( -1, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    RetValue = Abc_NtkOrchLocal( pNtk, fUseZeros_rwr, fUseZeros_ref, fPlaceEnable, nCutsMax, nNodesMax, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose, nNodeSizeMax, nConeSizeMax, fUseDcs );
    if ( RetValue == -1 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
    }
    else
    {
        Abc_NtkDelete( pDup );
        if ( RetValue == 0 )
        {
            Abc_Print( 0, "Ochestration (local greedy) has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: orchestrate [-KNFZzlvwh]\n" );
    Abc_Print( -2, "\t           performs technology-independent AIG synthesis using orchestration method (currently orchestrating rw/rf/rs)\n" );
    Abc_Print( -2, "\t-K <num> : (resub)the max cut size (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );
    Abc_Print( -2, "\t-N <num> : (resub)the max number of nodes to add (0 <= num <= 3) [default = %d]\n", nNodesMax );
    Abc_Print( -2, "\t-F <num> : (resub)the number of fanout levels for ODC computation [default = %d]\n", nLevelsOdc );
    Abc_Print( -2, "\t-l       : (resub/rw/refactor)toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : (rw)toggle using zero-cost replacements [default = %s]\n", fUseZeros_rwr? "yes": "no" );
    Abc_Print( -2, "\t-Z       : (refactor)toggle using zero-cost replacements [default = %s]\n", fUseZeros_ref? "yes": "no" );
    Abc_Print( -2, "\t-v       : (resub/rw/refactor)toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : (resub/rw/refactor)toggle detailed verbose printout [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description [AIG RTL Augmentation]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAIGAugmentation( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;
    int nNodeSizeMax;
    int nConeSizeMax;
    int fUpdateLevel;
    int fUseZeros_rwr;
    int fUseZeros_ref;
    int fUseDcs;
    int fVerbose;
    int RS_CUT_MIN =  4;
    int RS_CUT_MAX = 16;

    int fPrecompute;
    int fPlaceEnable;
    int nNodesMax;
    int nCutsMax;
    int nLevelsOdc;
    int fVeryVerbose;
    int Rand_Seed;
    //int sOpsOrder;
    size_t NtkSize;
    char *DecisionFile = NULL;
    Vec_Int_t *DecisionMask;
    Vec_Int_t *pGain_rwr;
    Vec_Int_t *pGain_res;
    Vec_Int_t *pGain_ref;    
    //FILE *maskFile;
    extern void Rwr_Precompute();
    extern int Abc_NtkOrchRand( Abc_Ntk_t * pNtk, Vec_Int_t **pGain_rwr, Vec_Int_t **pGain_res,Vec_Int_t **pGain_ref, Vec_Int_t **DecisionMask, char *DecisionFile, int Rand_Seed, int fUseZeros_rwr, int fUseZeros_ref, int fPlaceEnable, int nCutsMax, int nNodesMax, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int nNodeSizeMax, int nConeSizeMax, int fUseDcs );
    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros_rwr =  0;
    fUseZeros_ref =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    fVeryVerbose = 0;
    fPlaceEnable = 0;
    fPrecompute  = 0;
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;
    Rand_Seed = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "zZdsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        case 'z':
            fUseZeros_rwr ^= 1;
            break;
        case 'Z':
            fUseZeros_ref ^= 1;
            break;
        case 'd':
            if ( globalUtilOptind >= argc )
            {
                goto usage;
            }
            DecisionFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 's':
            if ( globalUtilOptind >= argc )
            {
                goto usage;
            }
            Rand_Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        }
    }
    if ( fPrecompute )
    {
        Rwr_Precompute();
        return 0;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < RS_CUT_MIN || nCutsMax > RS_CUT_MAX )
    {
        Abc_Print( -1, "Can only compute cuts for %d <= K <= %d.\n", RS_CUT_MIN, RS_CUT_MAX );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }
    if ( nNodeSizeMax > 15 )
    {
        Abc_Print( -1, "The cone size cannot exceed 15.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        Abc_Print( -1, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }
    NtkSize = Abc_NtkObjNumMax(pNtk);

    DecisionMask = Vec_IntAlloc(1);
    for (int i=0; i<NtkSize;i++){
           Vec_IntPush(DecisionMask, atoi("-1"));}
    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    RetValue = Abc_NtkOrchRand( pNtk, &pGain_rwr, &pGain_res, &pGain_ref, &DecisionMask, DecisionFile, Rand_Seed, fUseZeros_rwr, fUseZeros_ref, fPlaceEnable, nCutsMax, nNodesMax, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose, nNodeSizeMax, nConeSizeMax, fUseDcs );
    //printf("Vector check: %d %d\n", DecisionList->nSize, DecisionList->pArray[0]); 
    if ( RetValue == -1 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
    }
    else
    {
        Abc_NtkDelete( pDup );
        if ( RetValue == 0 )
        {
            Abc_Print( 0, "Orchestration evaluation for RL has failed.\n" );
            return 1;
        }
    }
    // Vec_IntPrint(pGain_rwr);
    return 0;

usage:
    Abc_Print( -2, "usage: aigaug [-s <num>] [-d <file>][-zZdsh]\n" );
    Abc_Print( -2, "\t           performs technology-independent AIG random synthesis (node level) for RTL augmentation\n" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements for rwr for aigaug [default = %s]\n", fUseZeros_rwr? "yes": "no" );
    Abc_Print( -2, "\t-Z       : toggle using zero-cost replacements for ref for aigaug [default = %s]\n", fUseZeros_ref? "yes": "no" );
    Abc_Print( -2, "\t-d       : record random synthesis decision made during augmentation [required filename; e.g., test.csv]\n");
    Abc_Print( -2, "\t-s       : set the random seed for random augmentation\n");
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\tExample       : read i10.aig;st;aigaug -s 1 -d test.csv;write i10_arg_1.aig;cec i10.aig i10_arg_1.aig\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;
    int fUpdateLevel;
    int fPrecompute;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    int fPlaceEnable;
    // external functions
    extern void Rwr_Precompute();

    // set defaults
    fUpdateLevel = 1;
    fPrecompute  = 0;
    fUseZeros    = 0;
    fVerbose     = 0;
    fVeryVerbose = 0;
    fPlaceEnable = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lxzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'x':
            fPrecompute ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'p':
            fPlaceEnable ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( fPrecompute )
    {
        Rwr_Precompute();
        return 0;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    RetValue = Abc_NtkRewrite( pNtk, fUpdateLevel, fUseZeros, fVerbose, fVeryVerbose, fPlaceEnable );
    if ( RetValue == -1 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
    }
    else
    {
        Abc_NtkDelete( pDup );
        if ( RetValue == 0 )
        {
            Abc_Print( 0, "Rewriting has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: rewrite [-lzvwh]\n" );
    Abc_Print( -2, "\t         performs technology-independent rewriting of the AIG\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printout subgraph statistics [default = %s]\n", fVeryVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-p     : toggle placement-aware rewriting [default = %s]\n", fPlaceEnable? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;
    int nNodeSizeMax;
    int nMinSaved;
    int nConeSizeMax;
    int fUpdateLevel;
    int fUseZeros;
    int fUseDcs;
    int fVerbose;
    extern int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nMinSaved, int nConeSizeMax, int fUpdateLevel, int fUseZeros, int fUseDcs, int fVerbose );

    // set defaults
    nNodeSizeMax = 10;
    nMinSaved    =  1;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMClzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeSizeMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMinSaved = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMinSaved < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConeSizeMax < 0 )
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'd':
            fUseDcs ^= 1;
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
    if ( fUseZeros )
        nMinSaved = 0;
    if ( nMinSaved == 0 )
        fUseZeros = 1;

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }
    if ( nNodeSizeMax > 15 )
    {
        Abc_Print( -1, "The cone size cannot exceed 15.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        Abc_Print( -1, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    RetValue = Abc_NtkRefactor( pNtk, nNodeSizeMax, nMinSaved, nConeSizeMax, fUpdateLevel, fUseZeros, fUseDcs, fVerbose );
    if ( RetValue == -1 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
    }
    else
    {
        Abc_NtkDelete( pDup );
        if ( RetValue == 0 )
        {
            Abc_Print( 0, "Refactoring has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: refactor [-NM <num>] [-lzvh]\n" );
    Abc_Print( -2, "\t           performs technology-independent refactoring of the AIG\n" );
    Abc_Print( -2, "\t-N <num> : the max support of the collapsed node [default = %d]\n", nNodeSizeMax );
    Abc_Print( -2, "\t-M <num> : the min number of nodes saved after one step (0 <= num) [default = %d]\n", nMinSaved );
//    Abc_Print( -2, "\t-C <num> : the max support of the containing cone [default = %d]\n", nConeSizeMax );
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
//    Abc_Print( -2, "\t-d       : toggle using don't-cares [default = %s]\n", fUseDcs? "yes": "no" );
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
int Abc_CommandRestructure( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nCutsMax;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    extern int Abc_NtkRestructure( Abc_Ntk_t * pNtk, int nCutsMax, int fUpdateLevel, int fUseZeros, int fVerbose );

    // set defaults
    nCutsMax      =  5;
    fUpdateLevel =  0;
    fUseZeros    =  0;
    fVerbose     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Klzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 )
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
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
    if ( nCutsMax < 4 || nCutsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", 4, CUT_SIZE_MAX );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRestructure( pNtk, nCutsMax, fUpdateLevel, fUseZeros, fVerbose ) )
    {
        Abc_Print( -1, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: restructure [-K <num>] [-lzvh]\n" );
    Abc_Print( -2, "\t           performs technology-independent restructuring of the AIG\n" );
    Abc_Print( -2, "\t-K <num> : the max cut size (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, nCutsMax );
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
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
int Abc_CommandRr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, Window;
    int nFaninLevels;
    int nFanoutLevels;
    int fUseFanouts;
    int fVerbose;
    extern int Abc_NtkRR( Abc_Ntk_t * pNtk, int nFaninLevels, int nFanoutLevels, int fUseFanouts, int fVerbose );

    // set defaults
    nFaninLevels  = 3;
    nFanoutLevels = 3;
    fUseFanouts   = 0;
    fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Wfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            Window = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Window < 0 )
                goto usage;
            nFaninLevels  = Window / 10;
            nFanoutLevels = Window % 10;
            break;
        case 'f':
            fUseFanouts ^= 1;
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

    printf( "This command is obsolete." );
    printf( "To perform pure redudancy removal, try \"mfs -r\".\n" );
    printf( "To perform something a little stronger try \"mfs2\"\n" );
    printf( "When working with an AIG, use \"logic\" before and \"strash\" after this command.\n" );
    return 0;

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRR( pNtk, nFaninLevels, nFanoutLevels, fUseFanouts, fVerbose ) )
    {
        Abc_Print( -1, "Redundancy removal has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: rr [-W NM] [-fvh]\n" );
    Abc_Print( -2, "\t         removes combinational redundancies in the current network\n" );
    Abc_Print( -2, "\t-W NM  : window size: TFI (N) and TFO (M) logic levels [default = %d%d]\n", nFaninLevels, nFanoutLevels );
    Abc_Print( -2, "\t-f     : toggle RR w.r.t. fanouts [default = %s]\n", fUseFanouts? "yes": "no" );
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
int Abc_CommandIRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewrite( Abc_Ntk_t * pNtk, int fUpdateLevel, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 1;
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

    pNtkRes = Abc_NtkIvyRewrite( pNtk, fUpdateLevel, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: irw [-lzvh]\n" );
    Abc_Print( -2, "\t         perform combinational AIG rewriting\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandDRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Dar_RwrPar_t Pars, * pPars = &Pars;
    int c, fRewriteOption = 0;

    extern Abc_Ntk_t * Abc_NtkDRewrite( Abc_Ntk_t * pNtk, Dar_RwrPar_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dar_ManDefaultRwrParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CNMKflzrvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            fRewriteOption = 1;
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 )
                goto usage;
            break;
        case 'N':
            fRewriteOption = 1;
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSubgMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSubgMax < 0 )
                goto usage;
            break;
        case 'M':
            fRewriteOption = 1;
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMinSaved = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMinSaved < 0 )
                goto usage;
            break;
        case 'f':
            fRewriteOption = 1;
            pPars->fFanout ^= 1;
            break;
        case 'l':
            pPars->fUpdateLevel ^= 1;
            break;
        case 'z':
            fRewriteOption = 1;
            pPars->fUseZeros ^= 1;
            break;
        case 'r':
            fRewriteOption = 1;
            pPars->fRecycle ^= 1;
            break;
        case 'K':
        {
            char * pEnd;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            errno = 0;
            Value = strtol( argv[globalUtilOptind++], &pEnd, 10 );
            if ( errno || pEnd == argv[globalUtilOptind-1] ||
                 *pEnd || (Value != 0 && Value < 4) || Value > 10 ) goto usage;
            pPars->nResubCutSize = (int)Value;
            break;
        }
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            fRewriteOption = 1;
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( (pPars->nResubCutSize && fRewriteOption) ||
         globalUtilOptind != argc ) goto usage;
    if ( pPars->fUseZeros )
        pPars->nMinSaved = 0;
    if ( pPars->nMinSaved == 0 )
        pPars->fUseZeros = 1;
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
    pNtkRes = Abc_NtkDRewrite( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return pPars->nResubCutSize ? 1 : 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drw [-C num] [-NM num] [-flzrvwh] | drw -K 4..10 [-lv]\n" );
    Abc_Print( -2, "\t         performs combinational AIG rewriting\n" );
    Abc_Print( -2, "\t-C num : the max number of cuts at a node [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-N num : the max number of subgraphs tried [default = %d]\n", pPars->nSubgMax );
    Abc_Print( -2, "\t-M num : the min number of nodes saved after one step (0 <= num) [default = %d]\n", pPars->nMinSaved );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", pPars->fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle representing fanouts [default = %s]\n", pPars->fFanout? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", pPars->fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using cut recycling [default = %s]\n", pPars->fRecycle? "yes": "no" );
    Abc_Print( -2, "\t-K num : use resubstitution with 4..10 cut leaves (0 = rewriting) [default = %d]\n", pPars->nResubCutSize );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose printout [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Dar_RefPar_t Pars, * pPars = &Pars;
    int c;

    extern Abc_Ntk_t * Abc_NtkDRefactor( Abc_Ntk_t * pNtk, Dar_RefPar_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dar_ManDefaultRefParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MKCelzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMffcMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMffcMin < 0 )
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLeafMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLeafMax < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 )
                goto usage;
            break;
        case 'e':
            pPars->fExtend ^= 1;
            break;
        case 'l':
            pPars->fUpdateLevel ^= 1;
            break;
        case 'z':
            pPars->fUseZeros ^= 1;
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
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    if ( pPars->nLeafMax < 4 || pPars->nLeafMax > 15 )
    {
        Abc_Print( -1, "This command only works for cut sizes 4 <= K <= 15.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDRefactor( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drf [-M num] [-K num] [-C num] [-elzvwh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG refactoring\n" );
    Abc_Print( -2, "\t-M num : the min MFFC size to attempt refactoring [default = %d]\n", pPars->nMffcMin );
    Abc_Print( -2, "\t-K num : the max number of cuts leaves [default = %d]\n", pPars->nLeafMax );
    Abc_Print( -2, "\t-C num : the max number of cuts to try at a node [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-e     : toggle extending tbe cut below MFFC [default = %s]\n", pPars->fExtend? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", pPars->fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", pPars->fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose printout [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDc2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, fUpdateLevel, fFanout, fPower, c;

    extern Abc_Ntk_t * Abc_NtkDC2( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fFanout, int fPower, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance     = 0;
    fVerbose     = 0;
    fUpdateLevel = 0;
    fFanout      = 1;
    fPower       = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "blfpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBalance ^= 1;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'f':
            fFanout ^= 1;
            break;
        case 'p':
            fPower ^= 1;
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
    pNtkRes = Abc_NtkDC2( pNtk, fBalance, fUpdateLevel, fFanout, fPower, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dc2 [-blfpvh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG optimization\n" );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle updating level [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle representing fanouts [default = %s]\n", fFanout? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", fPower? "yes": "no" );
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
int Abc_CommandDrwsat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, c;

    extern Abc_Ntk_t * Abc_NtkDrwsat( Abc_Ntk_t * pNtk, int fBalance, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBalance ^= 1;
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
    pNtkRes = Abc_NtkDrwsat( pNtk, fBalance, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drwsat [-bvh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG optimization for SAT\n" );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
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
int Abc_CommandIResyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyResyn( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 1;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvh" ) ) != EOF )
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

    pNtkRes = Abc_NtkIvyResyn( pNtk, fUpdateLevel, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: iresyn [-lvh]\n" );
    Abc_Print( -2, "\t         performs combinational resynthesis\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandRewire( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t *Abc_ManRewire(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose);
    Abc_Ntk_t *pNtk, *pTemp;
    Gia_Man_t *pExc = NULL;
    FILE *pFile = NULL;
    int c, nIters = 100000, nExpands = 128, nGrowth = 4, nDivs = -1, nFaninMax = 8, nSeed = 1, nTimeOut = 0, nVerbose = 1, nMode = 0, nMappedMode = 0, nDist = 0, fCheck = 0, fDch = 1, fTiming = 0;
    float nLevelGrowRatio = 0;
    Extra_UtilGetoptReset();

    pNtk = Abc_FrameReadNtk(pAbc);

    while ( ( c = Extra_UtilGetopt( argc, argv, "IEGDFSTMALRCVdtch" ) ) != EOF ) {
        switch ( c ) {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nExpands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nGrowth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDivs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMappedMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive number.\n" );
                goto usage;
            }
            nLevelGrowRatio = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            pFile = fopen( argv[globalUtilOptind], "rb" );
            if ( pFile == NULL )
            {
                Abc_Print( -1, "Cannot open input file \"%s\".\n", argv[globalUtilOptind] );
                return 1;
            }
            fclose( pFile );
            pExc = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
            if ( pExc == NULL )
            {
                Abc_Print( -1, "Reading AIGER has failed.\n" );
                return 1;
            }
            globalUtilOptind++;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'c':
            fCheck ^= 1;
            break;
        case 'd':
            fDch ^= 1;
            break;
        case 't':
            fTiming ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nMode == 0 && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Rewiring operates only on specific network representations. Use \"strash\" to apply it to an AIG, or add the \"-M 1\" flag to enable it for a mapped network.\n" );
        return 1;
    }
    if ( nMode == 1 && Abc_FrameReadLibGen2() == NULL )
    {
        Abc_Print( -1, "Library is not available.\n" );
        return 1;
    }

    pTemp = Abc_ManRewire( pNtk, pExc, nIters, nLevelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, nSeed, fCheck, nVerbose );
    if ( pExc )
        Gia_ManStop( pExc );
    Abc_FrameReplaceCurrentNetwork( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: rewire [-IEGDFLRMASTV <num>]\n" );
    Abc_Print( -2, "\t-I <num>  :  the number of iterations [default = %d]\n",                                  nIters );
    Abc_Print( -2, "\t-E <num>  :  the number of fanins to add to all nodes [default = %d]\n",                  nExpands );
    Abc_Print( -2, "\t-G <num>  :  the number of fanins to add to one node [default = %d]\n",                   nGrowth );
    Abc_Print( -2, "\t-D <num>  :  the number of shared divisors to extract (-1: unlimited) [default = %d]\n",  nDivs );
    Abc_Print( -2, "\t-F <num>  :  the limit on the fanin count at a node [default = %d]\n",                    nFaninMax);
    Abc_Print( -2, "\t-L <num>  :  localization distances (0: unlimited) [default = %d]\n",                     nDist);
    Abc_Print( -2, "\t-R <num>  :  level constraint (0: unlimited, 1: preserve level) [default = %g]\n",        nLevelGrowRatio);
    Abc_Print( -2, "\t-M <num>  :  optimization target [default = %s]\n",                                       nMode ? "mapped" : "AIG" );
    Abc_Print( -2, "\t-A <num>  :  mapper (0: amap, 1: &nf, 2: &simap) (experimental) [default = %d]\n",        nMappedMode );
    Abc_Print( -2, "\t-C <file> :  AIGER specifying external cares\n");
    Abc_Print( -2, "\t-S <num>  :  the random seed (0: random, >= 1: user defined) [default = %d]\n",           nSeed );
    Abc_Print( -2, "\t-T <num>  :  the timeout in seconds (0: unlimited) [default = %d]\n",                     nTimeOut );
    Abc_Print( -2, "\t-V <num>  :  the verbosity level [default = %d]\n",                                       nVerbose );
    Abc_Print( -2, "\t-c        :  check the equivalence [default = %s]\n",                                     fCheck ? "yes" : "no" );
    Abc_Print( -2, "\t-d        :  toggle perform \"dch\" before mapping [default = %s]\n",                     fDch ? "yes" : "no" );
    Abc_Print( -2, "\t-t        :  toggle timing-driven rewiring [default = %s]\n",                             fTiming ? "yes" : "no" );
    Abc_Print( -2, "\t-h        :  prints the command usage\n" );
    Abc_Print( -2, "\n\tThis command was contributed by Jiun-Hao Chen from National Taiwan University.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9RexWalk( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManAutomWalk( Gia_Man_t * p, int nSteps, int nWalks, int fVerbose );
    int c, nSteps = 50, nWalks = 5, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nSteps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSteps < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nWalks = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWalks < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Show(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManAutomWalk( pAbc->pGia, nSteps, nWalks, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &rexwalk [-SR] [-vh]\n" );
    Abc_Print( -2, "\t         performs simulation of an AIG representing a regular expression\n" );
    Abc_Print( -2, "\t-S num : the number of steps to take [default = %d]\n", nSteps );
    Abc_Print( -2, "\t-R num : the number of walks to make [default = %d]\n", nWalks );
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
int Abc_CommandAbc9Resyn3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManResyn3( Gia_Man_t * pGia, int fVerbose );
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
        Abc_Print( -1, "Abc_CommandAbc9Resyn3(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManResyn3( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &resyn3 [-vh]\n" );
    Abc_Print( -2, "\t         performs rewriting of the AIG while preserving logic level\n" );
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
int Abc_CommandAbc9Resyn3rs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCompress3rs( Gia_Man_t * pGia, int fUpdateLevel, int fVerbose );
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
        Abc_Print( -1, "Abc_CommandAbc9Resyn3rs(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManCompress3rs( pAbc->pGia, 1, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &resyn3rs [-vh]\n" );
    Abc_Print( -2, "\t         performs rewriting of the AIG while preserving logic level\n" );
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
int Abc_CommandAbc9Compress3rs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCompress3rs( Gia_Man_t * pGia, int fUpdateLevel, int fVerbose );
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
        Abc_Print( -1, "Abc_CommandAbc9Compress3rs(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManCompress3rs( pAbc->pGia, 0, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &compress3rs [-vh]\n" );
    Abc_Print( -2, "\t         performs rewriting of the AIG without preserving logic level\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Orchestrates fast GIA-based area optimization.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dc3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDc3( Gia_Man_t * pGia, int fKeepLevel, int fVerbose );
    Gia_Man_t * pNew;
    int c, fKeepLevel = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "lvh")) != EOF )
    {
        switch ( c )
        {
        case 'l': fKeepLevel ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&dc3: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManHasChoices(pAbc->pGia) || Gia_ManMuxNum(pAbc->pGia) ||
         Gia_ManXorNum(pAbc->pGia) || Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&dc3: This command requires an AIG without choices, XOR/MUX nodes, or barrier buffers.\n" );
        return 1;
    }
    pNew = Gia_ManDc3( pAbc->pGia, fKeepLevel, fVerbose );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "&dc3: Optimization has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &dc3 [-lvh]\n" );
    Abc_Print( -2, "\t         performs fast orchestrated AIG area optimization\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fKeepLevel ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dc2( Abc_Frame_t * pAbc, int argc, char ** argv )
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
        Abc_Print( -1, "Abc_CommandAbc9Dc2(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManCompress2( pAbc->pGia, fUpdateLevel, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dc2 [-lvh]\n" );
    Abc_Print( -2, "\t         performs heavy rewriting of the AIG\n" );
    Abc_Print( -2, "\t-l     : toggle level update during rewriting [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandAbc9Shrink( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int nLutSize;
    int c,fVerbose = 0;
    int fKeepLevel = 0;
    int nFanoutMax = 50;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nlvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a char string.\n" );
                goto usage;
            }
            nFanoutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFanoutMax < 0 )
                goto usage;
            break;
        case 'l':
            fKeepLevel ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): There is no AIG.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    nLutSize = Gia_ManLutSizeMax( pAbc->pGia );
    if ( nLutSize <= 4 )
        pTemp = Gia_ManMapShrink4( pAbc->pGia, fKeepLevel, fVerbose );
    else if ( nLutSize <= 6 )
        pTemp = Gia_ManMapShrink6( pAbc->pGia, nFanoutMax, fKeepLevel, fVerbose );
    else
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): Works only for 4-LUTs and 6-LUTs.\n" );
    if ( pTemp )
        Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &shrink [-N num] [-lvh]\n" );
    Abc_Print( -2, "\t         performs fast shrinking using current mapping\n" );
    Abc_Print( -2, "\t-N num : the max fanout count to skip a divisor [default = %d]\n", nFanoutMax );
    Abc_Print( -2, "\t-l     : toggle level update during shrinking [default = %s]\n", fKeepLevel? "yes": "no" );
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
int Abc_CommandAbc9Balance( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int nNewNodesMax = ABC_INFINITY;
    int fDelayOnly   = 0;
    int fSimpleAnd   = 0;
    int fStrict      = 0;
    int fKeepLevel   = 0;
    int c, fVerbose  = 0;
    int fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ndaslvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a char string.\n" );
                goto usage;
            }
            nNewNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNewNodesMax < 0 )
                goto usage;
            break;
        case 'd':
            fDelayOnly ^= 1;
            break;
        case 'a':
            fSimpleAnd ^= 1;
            break;
        case 's':
            fStrict ^= 1;
            break;
        case 'l':
            fKeepLevel ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Balance(): There is no AIG.\n" );
        return 1;
    }
    if ( fDelayOnly )
        pTemp = Gia_ManBalance( pAbc->pGia, fSimpleAnd, fStrict, fVerbose );
    else
        pTemp = Gia_ManAreaBalance( pAbc->pGia, fSimpleAnd, nNewNodesMax, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &b [-N num] [-dasvwh]\n" );
    Abc_Print( -2, "\t         performs AIG balancing to reduce delay and area\n" );
    Abc_Print( -2, "\t-N num : the max fanout count to skip a divisor [default = %d]\n", nNewNodesMax );
    Abc_Print( -2, "\t-d     : toggle delay only balancing [default = %s]\n", fDelayOnly? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using AND instead of AND/XOR/MUX [default = %s]\n", fSimpleAnd? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle strict control of area in delay-mode (\"&b -d\") [default = %s]\n", fStrict? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
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
int Abc_CommandAbc9BalanceLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManBalanceLut( Gia_Man_t * p, int nLutSize, int nCutNum, int fVerbose );
    extern Gia_Man_t * Gia_ManLutBalance( Gia_Man_t * p, int nLutSize, int fUseMuxes, int fRecursive, int fOptArea, int fVerbose );
    Gia_Man_t * pTemp = NULL;
    int fUseOld      = 0;
    int nLutSize     = 6;
    int nCutNum      = 8;
    int fUseMuxes    = 1;
    int fRecursive   = 1;
    int fOptArea     = 1;
    int c, fVerbose  = 0;
    int fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCnmravwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a char string.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 2 || nLutSize >= 16 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a char string.\n" );
                goto usage;
            }
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
                goto usage;
            break;
        case 'n':
            fUseOld ^= 1;
            break;
        case 'm':
            fUseMuxes ^= 1;
            break;
        case 'r':
            fRecursive ^= 1;
            break;
        case 'a':
            fOptArea ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9BalanceLut(): There is no AIG.\n" );
        return 1;
    }
    if ( fUseOld )
        pTemp = Gia_ManBalanceLut( pAbc->pGia, nLutSize, nCutNum, fVerbose );
    else
        pTemp = Gia_ManLutBalance( pAbc->pGia, nLutSize, fUseMuxes, fRecursive, fOptArea, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &blut [-KC num] [-mravh]\n" );
    Abc_Print( -2, "\t           performs AIG balancing for the given LUT size\n" );
    Abc_Print( -2, "\t-K num   : LUT size for the mapping (2 <= K <= %d) [default = %d]\n", 6, nLutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (1 <= C <= %d) [default = %d]\n", 8, nCutNum );
    Abc_Print( -2, "\t-m       : toggle performing MUX restructuring [default = %s]\n", fUseMuxes? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggle performing recursive restructuring [default = %s]\n", fRecursive? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggle performing area-oriented restructuring [default = %s]\n", fOptArea? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-w       : toggle printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Reshape( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManReshape1( Gia_Man_t * pGia, int fUseSimple, int fVerbose, int fVeryVerbose );
    extern Gia_Man_t * Gia_ManReshape2( Gia_Man_t * pGia, int fUseSimple, int fVerbose, int fVeryVerbose );
    Gia_Man_t * pTemp;
    int fUseReshape1 =  0;
    int fUseSimple   =  0;
    int c, fVerbose  =  0;
    int fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "asvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fUseReshape1 ^= 1;
            break;
        case 's':
            fUseSimple ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Resub(): There is no AIG.\n" );
        return 1;
    }
    if ( fUseReshape1 )
        pTemp = Gia_ManReshape1( pAbc->pGia, fUseSimple, fVerbose, fVeryVerbose );
    else
        pTemp = Gia_ManReshape2( pAbc->pGia, fUseSimple, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &reshape [-asvwh]\n" );
    Abc_Print( -2, "\t           performs AIG resubstitution\n" );
    Abc_Print( -2, "\t-a       : toggles selecting the algorithm [default = %s]\n",         fUseReshape1? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles using simple method [default = %s]\n",             fUseSimple? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Syn2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose  =  0;
    int fOldAlgo     =  0;
    int fCoarsen     =  1;
    int fCutMin      =  0;
    int nRelaxRatio  = 20;
    int fDelayMin    =  0;
    int fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Rakmdvwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'a':
            fOldAlgo ^= 1;
            break;
        case 'k':
            fCoarsen ^= 1;
            break;
        case 'm':
            fCutMin ^= 1;
            break;
        case 'd':
            fDelayMin ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Syn2(): There is no AIG.\n" );
        return 1;
    }
    if ( fDelayMin )
    {
        If_DsdMan_t * p = (If_DsdMan_t *)Abc_FrameReadManDsd();
        if ( p && If_DsdManVarNum(p) < 6 )
        {
            printf( "DSD manager has incompatible number of variables. Delay minimization is not performed.\n" );
            fDelayMin = 0;
        }
    }
    pTemp = Gia_ManAigSyn2( pAbc->pGia, fOldAlgo, fCoarsen, fCutMin, nRelaxRatio, fDelayMin, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &syn2 [-R num] [-akmdvh]\n" );
    Abc_Print( -2, "\t           performs AIG optimization\n" );
    Abc_Print( -2, "\t-R num   : the delay relaxation ratio (num >= 0) [default = %d]\n",   nRelaxRatio );
    Abc_Print( -2, "\t-a       : toggles using the old algorithm [default = %s]\n",         fOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles coarsening the subject graph [default = %s]\n",    fCoarsen? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles cut minimization [default = %s]\n",                fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles additional delay optimization [default = %s]\n",   fDelayMin? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Syn3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "Abc_CommandAbc9Syn3(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManAigSyn3( pAbc->pGia, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &syn3 [-lvh]\n" );
    Abc_Print( -2, "\t         performs AIG optimization\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
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
int Abc_CommandAbc9Syn4( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "Abc_CommandAbc9Syn4(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManAigSyn4( pAbc->pGia, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &syn4 [-lvh]\n" );
    Abc_Print( -2, "\t         performs AIG optimization\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs compact AIG rewriting using one cut per node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Drw( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pNew;
    int c, fKeepLevel = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "lvh")) != EOF )
    {
        switch ( c )
        {
        case 'l': fKeepLevel ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&drw: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManHasChoices(pAbc->pGia) || pAbc->pGia->pMuxes || Gia_ManXorNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&drw: This command requires an AIG without choices or XOR/MUX nodes.\n" );
        return 1;
    }
    pNew = Drw_ManRewrite( pAbc->pGia, fKeepLevel, fVerbose );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "&drw: Rewriting has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &drw [-lvh]\n" );
    Abc_Print( -2, "\t         performs one pass of AIG rewriting using one cut per node\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fKeepLevel ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Refactors an AIG using cached truth-table factorizations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Drf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pNew;
    int c, fKeepLevel = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "lvh")) != EOF )
    {
        switch ( c )
        {
        case 'l': fKeepLevel ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&drf: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManHasChoices(pAbc->pGia) || Gia_ManMuxNum(pAbc->pGia) || Gia_ManXorNum(pAbc->pGia) || Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&drf: This command requires an AIG without choices, XOR/MUX nodes, or barrier buffers.\n" );
        return 1;
    }
    pNew = Drf_ManRefactor( pAbc->pGia, fKeepLevel, fVerbose );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "&drf: Refactoring has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &drf [-lvh]\n" );
    Abc_Print( -2, "\t         performs one pass of AIG refactoring with cached factorizations\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fKeepLevel ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LNetOpt( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManPerformLNetOpt( Gia_Man_t * p, int fTryNew, char * pFileName, int nIns, int nOuts, int Thresh, int nRounds, int fVerbose );
    extern Gia_Man_t * Gia_ManPerformLNetOptNew( Gia_Man_t * p, char * pFileName, int nIns, int nOuts, int Thresh, int nRounds, int fVerbose );
    Gia_Man_t * pTemp;
    char * pFileName = NULL;
    int c, nIns = 6, nOuts = 2, Limit = 0, nRounds = 20, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IORXvh" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
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
    if ( argc > globalUtilOptind + 1 )
    {
        return 0;
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
    pTemp = Gia_ManPerformLNetOptNew( pAbc->pGia, pFileName, nIns, nOuts, Limit, nRounds, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &lnetopt [-IORX num] [-vh] <file>\n" );
    Abc_Print( -2, "\t           performs specialized AIG optimization\n" );
    Abc_Print( -2, "\t-I num   : the input support size [default = %d]\n",                 nIns );
    Abc_Print( -2, "\t-O num   : the output group size [default = %d]\n",                  nOuts );
    Abc_Print( -2, "\t-R num   : patterns are cares starting this value [default = %d]\n", Limit );
    Abc_Print( -2, "\t-X num   : the number of optimization rounds [default = %d]\n",      nRounds );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n",                 fVerbose? "yes": "no" );
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
int Abc_CommandAbc9Ttopt( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    char * pFileName = NULL;
    int c, nIns = 6, nOuts = 2, Limit = 0, nRounds = 20, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IORXvh" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
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
    if ( argc > globalUtilOptind + 1 )
    {
        return 0;
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
    if ( pFileName )
        pTemp = Gia_ManTtoptCare( pAbc->pGia, nIns, nOuts, nRounds, pFileName, Limit );
    else
        pTemp = Gia_ManTtopt( pAbc->pGia, nIns, nOuts, nRounds );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &ttopt [-IORX num] [-vh] <file>\n" );
    Abc_Print( -2, "\t           performs specialized AIG optimization\n" );
    Abc_Print( -2, "\t-I num   : the input support size [default = %d]\n",                 nIns );
    Abc_Print( -2, "\t-O num   : the output group size [default = %d]\n",                  nOuts );
    Abc_Print( -2, "\t-R num   : patterns are cares starting this value [default = %d]\n", Limit );
    Abc_Print( -2, "\t-X num   : the number of optimization rounds [default = %d]\n",      nRounds );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n",                 fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<file>   : file name with simulation information\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Yukio Miyasaka.\n" );
    Abc_Print( -2, "\t           The paper describing the method: Y. Miyasaka et al. \"Synthesizing\n" );
    Abc_Print( -2, "\t           a class of practical Boolean functions using truth tables\". Proc. IWLS 2022.\n" );
    Abc_Print( -2, "\t           https://people.eecs.berkeley.edu/~alanmi/publications/2022/iwls22_reo.pdf\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Transduction( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp, * pExdc = NULL;
    int c, nType = 1, fMspf = 0, nRandom = 0, nSortType = 0, nPiShuffle = 0, nParameter = 0, fLevel = 0, fTruth = 0, fNewLine = 0, nVerbose = 2;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TSIPRVtmnlh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nRandom = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nSortType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nPiShuffle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nParameter = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 't':
            fTruth ^= 1;
            break;
        case 'm':
            fMspf ^= 1;
            break;
        case 'n':
            fNewLine ^= 1;
            break;
        case 'l':
            fLevel ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
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
            Abc_Print( -1, "Cannot open input file \"%s\". ", argv[globalUtilOptind] );
            return 1;
        }
        fclose( pFile );
        pExdc = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
        if ( pExdc == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 1;
        }
    }

    if ( fLevel && (nType == 3 || nType == 8) )
    {
        Abc_Print( -1, "Level preserving optimization does not work with transduction type 3 and 8.\n" );
        return 1;
    }

    if ( fTruth )
        pTemp = Gia_ManTransductionTt( pAbc->pGia, nType, fMspf, nRandom, nSortType, nPiShuffle, nParameter, fLevel, pExdc, fNewLine, nVerbose );
    else
        pTemp = Gia_ManTransductionBdd( pAbc->pGia, nType, fMspf, nRandom, nSortType, nPiShuffle, nParameter, fLevel, pExdc, fNewLine, nVerbose );
    if ( pExdc != NULL )
        Gia_ManStop( pExdc );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &transduction [-TSIPRV num] [-bmlh] <file>\n" );
    Abc_Print( -2, "\t           performs transduction-based AIG optimization\n" );
    Abc_Print( -2, "\t-T num   : transduction type [default = %d]\n", nType );
    Abc_Print( -2, "\t                0: remove simply redundant nodes\n" );
    Abc_Print( -2, "\t                1: Resub\n" );
    Abc_Print( -2, "\t                2: ResubMono\n" );
    Abc_Print( -2, "\t                3: ResubShared\n" );
    Abc_Print( -2, "\t                4: repeat Resub\n" );
    Abc_Print( -2, "\t                5: repeat ResubMono\n" );
    Abc_Print( -2, "\t                6: script RepeatInner\n" );
    Abc_Print( -2, "\t                7: script RepeatOuter\n" );
    Abc_Print( -2, "\t                8: script RepeatAll\n" );
    Abc_Print( -2, "\t-S num   : fanin sort type [default = %d]\n", nSortType );
    Abc_Print( -2, "\t                0: topological order\n" );
    Abc_Print( -2, "\t                1: number of ones\n" );
    Abc_Print( -2, "\t                2: number of ones before complemented edges\n" );
    Abc_Print( -2, "\t                3: pseudo random\n" );
    Abc_Print( -2, "\t                4: no sorting\n" );
    Abc_Print( -2, "\t-I num   : random seed to shuffle PIs (0 = no shuffle) [default = %d]\n", nPiShuffle );
    Abc_Print( -2, "\t-P num   : parameters for scripts [default = %d]\n", nParameter );
    Abc_Print( -2, "\t-R num   : random seed to set all parameters (0 = no random) ([default = %d]\n", nRandom );
    Abc_Print( -2, "\t-V num   : verbosity level [default = %d]\n", nVerbose );
    Abc_Print( -2, "\t-t       : toggles using truth table instead of BDD [default = %s]\n", fTruth? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles using MSPF instead of CSPF [default = %s]\n", fMspf? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggles printing with a new line [default = %s]\n", fNewLine? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggles level preserving optimization [default = %s]\n", fLevel? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n" );
    Abc_Print( -2, "\t<file>   : AIGER specifying external don't-cares\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Yukio Miyasaka.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9TranStoch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManTranStoch( Gia_Man_t * pGia, int nRestarts, int nHops, int nSeedBase, int fMspf, int fMerge, int fResetHop, int fZeroCostHop, int fRefactor, int fTruth, int fSingle, int fOriginalOnly, int fNewLine, Gia_Man_t * pExdc, int nThreads, int nVerbose );
    Gia_Man_t * pTemp, * pExdc = NULL;
    int c, nRestarts = 0, nHops = 10, nSeedBase = 0, fMspf = 1, fMerge = 1, fResetHop = 1, fZeroCostHop = 0, fRefactor = 0, fTruth = 0, fSingle = 0, fOriginalOnly = 0, fNewLine = 0, nThreads = 1, nVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMRPVmgrzftsonh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nRestarts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nHops = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nSeedBase = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nThreads = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'm':
            fMspf ^= 1;
            break;
        case 'g':
            fMerge ^= 1;
            break;
        case 'r':
            fResetHop ^= 1;
            break;
        case 'z':
            fZeroCostHop ^= 1;
            break;
        case 'f':
            fRefactor ^= 1;
            break;
        case 't':
            fTruth ^= 1;
            break;
        case 's':
            fSingle ^= 1;
            break;
        case 'o':
            fOriginalOnly ^= 1;
            break;
        case 'n':
            fNewLine ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
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
            Abc_Print( -1, "Cannot open input file \"%s\". ", argv[globalUtilOptind] );
            return 1;
        }
        fclose( pFile );
        pExdc = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
        if ( pExdc == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 1;
        }
    }

    pTemp = Gia_ManTranStoch( pAbc->pGia, nRestarts, nHops, nSeedBase, fMspf, fMerge, fResetHop, fZeroCostHop, fRefactor, fTruth, fSingle, fOriginalOnly, fNewLine, pExdc, nThreads, nVerbose );
    if ( pExdc != NULL )
        Gia_ManStop( pExdc );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &transtoch [-NMRPV num] [-mgrzftsonh] <file>\n" );
    Abc_Print( -2, "\t           iterates transduction with randomized parameters\n" );
    Abc_Print( -2, "\t-N num   : number of restarts [default = %d]\n", nRestarts );
    Abc_Print( -2, "\t-M num   : number of hops (if; mfs2; strash) [default = %d]\n", nHops );
    Abc_Print( -2, "\t-R num   : random seed [default = %d]\n", nSeedBase );
    Abc_Print( -2, "\t-P num   : number of threads [default = %d]\n", nThreads );
    Abc_Print( -2, "\t-V num   : verbosity level [default = %d]\n", nVerbose);
    Abc_Print( -2, "\t-m       : toggles using MSPF instead of CSPF [default = %s]\n", fMspf? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles using ResubShared [default = %s]\n", fMerge? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggles resetting hop count when new minimum is found [default = %s]\n", fResetHop? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggles using \"drf -z\" instead of \"if;mfs2;st\" for hop [default = %s]\n", fZeroCostHop? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggles using \"drf -z\" instead of \"&dc2\" for ite [default = %s]\n", fRefactor? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggles using truth table instead of BDD [default = %s]\n", fTruth? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles starting from the smallest starting point [default = %s]\n", fSingle? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles starting from the given AIG [default = %s]\n", fOriginalOnly? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggles printing with a new line [default = %s]\n", fNewLine? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n" );
    Abc_Print( -2, "\t<file>   : AIGER specifying external don't-cares\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Yukio Miyasaka.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Rrr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t *pNew;
    int c;
    int iSeed = 0, nWords = 10, nTimeout = 0, nSchedulerVerbose = 0, nPartitionerVerbose = 0, nOptimizerVerbose = 0, nAnalyzerVerbose = 0, nSimulatorVerbose = 0, nSatSolverVerbose = 0, fUseBddCspf = 0, fUseBddMspf = 0, nConflictLimit = 0, nSortType = -1, nOptimizerFlow = 0, nSchedulerFlow = 0, nPartitionType = 0, nDistance = 0, nJobs = 1, nThreads = 1, nPartitionSize = 0, nPartitionSizeMin = 0, fDeterministic = 1, nParallelPartitions = 1, fOptOnInsert = 0, fGreedy = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "XYZNJKLBDRWTCGVPOAQSabdegh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'X':
            nOptimizerFlow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Y':
            nSchedulerFlow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Z':
            nPartitionType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'N':
            nJobs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'J':
            nThreads = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'K':
            nPartitionSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'L':
            nPartitionSizeMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'B':
            nParallelPartitions = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'D':
            nDistance = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            iSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'W':
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'T':
            nTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            nConflictLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'G':
            nSortType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'V':
            nSchedulerVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'P':
            nPartitionerVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'O':
            nOptimizerVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'A':
            nAnalyzerVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Q':
            nSimulatorVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            nSatSolverVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'a':
            fUseBddCspf ^= 1;
            break;
        case 'b':
            fUseBddMspf ^= 1;
            break;
        case 'd':
            fDeterministic ^= 1;
            break;
        case 'e':
            fOptOnInsert ^= 1;
            break;
        case 'g':
            fGreedy ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc > globalUtilOptind ) {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    
    if ( nSchedulerVerbose )
    {
        Abc_Print( 2, "Using the following parameters :\n" );
        Abc_Print( 2, "\t-X %3d : method ", nOptimizerFlow );
        switch( nOptimizerFlow )
        {
        case 0:
            Abc_Print( 2, "(0 = single-add resub)" );
            break;
        case 1:
            Abc_Print( 2, "(1 = multi-add resub)" );
            break;
        case 2:
            Abc_Print( 2, "(2 = repeat single-add and multi-add resubs)" );
            break;
        case 3:
            Abc_Print( 2, "(3 = random one meaningful resub)" );
            break;
        }
        Abc_Print( 2, "\n" );
        Abc_Print( 2, "\t-Y %3d : flow ", nSchedulerFlow );
        switch ( nSchedulerFlow )
        {
        case 0:
            Abc_Print( 2, "(0 = apply method once)" );
            break;
        case 1:
            Abc_Print( 2, "(1 = iterate like transtoch)" );
            break;
        case 2:
            Abc_Print( 2, "(2 = iterate like deepsyn)" );
            break;
        }
        Abc_Print( 2, "\n" );
        Abc_Print( 2, "\t-N %3d : number of jobs to create by restarting or partitioning\n", nJobs );
        Abc_Print( 2, "\t-J %3d : number of threads\n", nThreads );
        Abc_Print( 2, "\t-K %3d : maximum partition size (0 = no partitioning)\n", nPartitionSize );
        Abc_Print( 2, "\t-L %3d : minimum partition size\n", nPartitionSizeMin );
        Abc_Print( 2, "\t-B %3d : maximum number of partitions to optimize in parallel\n", nParallelPartitions );
        Abc_Print( 2, "\t-R %3d : random number generator seed\n", iSeed );
        Abc_Print( 2, "\t-T %3d : timeout in seconds (0 = no timeout)\n", nTimeout );
        Abc_Print( 2, "\t-C %3d : conflict limit (0 = no limit)\n", nConflictLimit );
        Abc_Print( 2, "Use command line switch \"-h\" to see more options\n\n" );
    }
    
    pNew = Gia_ManRrr( pAbc->pGia, iSeed, nWords, nTimeout, nSchedulerVerbose, nPartitionerVerbose, nOptimizerVerbose, nAnalyzerVerbose, nSimulatorVerbose, nSatSolverVerbose, fUseBddCspf, fUseBddMspf, nConflictLimit, nSortType, nOptimizerFlow, nSchedulerFlow, nPartitionType, nDistance, nJobs, nThreads, nPartitionSize, nPartitionSizeMin, fDeterministic, nParallelPartitions, fOptOnInsert, fGreedy );

    Abc_FrameUpdateGia( pAbc, pNew );
    
    return 0;

usage:
      Abc_Print( -2, "usage: rrr [-XYZNJKLBDRWTCGVPOAQS num] [-abdegh]\n" );
      Abc_Print( -2, "\t        perform optimization\n" );
      Abc_Print( -2, "\t-X num : method [default = %d]\n", nOptimizerFlow );
      Abc_Print( -2, "\t                0: single-add resub\n" );
      Abc_Print( -2, "\t                1: multi-add resub\n" );
      Abc_Print( -2, "\t                2: repeat 0 and 1\n" );
      Abc_Print( -2, "\t                3: random one meaningful resub\n" );
      Abc_Print( -2, "\t-Y num : flow [default = %d]\n", nSchedulerFlow );
      Abc_Print( -2, "\t                0: apply method once\n" );
      Abc_Print( -2, "\t                1: iterate like transtoch\n" );
      Abc_Print( -2, "\t                2: iterate like deepsyn\n" );
      Abc_Print( -2, "\t-Z num : partition [default = %d]\n", nPartitionType );
      Abc_Print( -2, "\t                0: distance base\n" );
      Abc_Print( -2, "\t                1: level base\n" );
      Abc_Print( -2, "\t-N num : number of jobs to create by restarting or partitioning [default = %d]\n", nJobs );
      Abc_Print( -2, "\t-J num : number of threads [default = %d]\n", nThreads );
      Abc_Print( -2, "\t-K num : maximum partition size (0 = no partitioning) [default = %d]\n", nPartitionSize );
      Abc_Print( -2, "\t-L num : minimum partition size [default = %d]\n", nPartitionSizeMin );
      Abc_Print( -2, "\t-B num : maximum number of partitions in parallel [default = %d]\n", nParallelPartitions );
      Abc_Print( -2, "\t-D num : maximum distance between node and new fanin (0 = no limit) [default = %d]\n", nDistance );
      Abc_Print( -2, "\t-R num : random number generator seed [default = %d]\n", iSeed );
      Abc_Print( -2, "\t-W num : number of simulation words [default = %d]\n", nWords );
      Abc_Print( -2, "\t-T num : timeout in seconds (0 = no timeout) [default = %d]\n", nTimeout );
      Abc_Print( -2, "\t-C num : conflict limit (0 = no limit) [default = %d]\n", nConflictLimit );
      Abc_Print( -2, "\t-G num : fanin cost function (-1 = random) [default = %d]\n", nSortType );
      Abc_Print( -2, "\t-V num : scheduler verbosity level [default = %d]\n", nSchedulerVerbose );
      Abc_Print( -2, "\t-P num : partitioner verbosity level [default = %d]\n", nPartitionerVerbose );
      Abc_Print( -2, "\t-O num : optimizer verbosity level [default = %d]\n", nOptimizerVerbose );
      Abc_Print( -2, "\t-A num : analyzer verbosity level [default = %d]\n", nAnalyzerVerbose );
      Abc_Print( -2, "\t-Q num : simulator verbosity level [default = %d]\n", nSimulatorVerbose );
      Abc_Print( -2, "\t-S num : SAT solver verbosity level [default = %d]\n", nSatSolverVerbose );
      Abc_Print( -2, "\t-a     : use BDD-based analyzer (CSPF) [default = %s]\n", fUseBddCspf? "yes": "no" );
      Abc_Print( -2, "\t-b     : use BDD-based analyzer (MSPF) [default = %s]\n", fUseBddMspf? "yes": "no" );
      Abc_Print( -2, "\t-d     : ensure deterministic execution [default = %s]\n", fDeterministic? "yes": "no" );
      Abc_Print( -2, "\t-e     : apply \"c2rs; dc2\" after importing changes of partitions [default = %s]\n", fOptOnInsert? "yes": "no" );
      Abc_Print( -2, "\t-g     : discard changes that increased the cost [default = %s]\n", fGreedy? "yes": "no" );
      Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Rewire( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t *Gia_ManRewire(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fChoices, int fVerbose);
    FILE *pFile = NULL;
    Gia_Man_t *pTemp, *pExc = NULL;
    int c, nIters = 100000, nExpands = 128, nGrowth = 4, nDivs = -1, nFaninMax = 8, nSeed = 1, nTimeOut = 0, nVerbose = 1, nMode = 0, nMappedMode = 0, nDist = 0, fCheck = 0, fChoices = 0, fDch = 1, fTiming = 0;
    float nLevelGrowRatio = 0;
    Extra_UtilGetoptReset();

    while ( ( c = Extra_UtilGetopt( argc, argv, "IEGDFSTMALRCVcsdth" ) ) != EOF ) {
        switch ( c ) {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nExpands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nGrowth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDivs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMappedMode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive number.\n" );
                goto usage;
            }
            nLevelGrowRatio = atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            pFile = fopen( argv[globalUtilOptind], "rb" );
            if ( pFile == NULL )
            {
                Abc_Print( -1, "Cannot open input file \"%s\".\n", argv[globalUtilOptind] );
                return 1;
            }
            fclose( pFile );
            pExc = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
            if ( pExc == NULL )
            {
                Abc_Print( -1, "Reading AIGER has failed.\n" );
                return 1;
            }
            globalUtilOptind++;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'c':
            fCheck ^= 1;
            break;
        case 's':
            fChoices ^= 1;
            break;
        case 'd':
            fDch ^= 1;
            break;
        case 't':
            fTiming ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty GIA network.\n" );
        return 1;
    }
    if ( nMode == 1 && Abc_FrameReadLibGen2() == NULL )
    {
        Abc_Print( -1, "Library is not available.\n" );
        return 1;
    }

    pTemp = Gia_ManRewire( pAbc->pGia, pExc, nIters, nLevelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, nSeed, fCheck, fChoices, nVerbose );
    if ( pExc )
        Gia_ManStop( pExc );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &rewire [-IEGDFLRMASTV <num>] [-csh]\n" );
    Abc_Print( -2, "\t             performs AIG re-wiring\n" );
    Abc_Print( -2, "\t-I <num>  :  the number of iterations [default = %d]\n",                                  nIters );
    Abc_Print( -2, "\t-E <num>  :  the number of fanins to add to all nodes [default = %d]\n",                  nExpands );
    Abc_Print( -2, "\t-G <num>  :  the number of fanins to add to one node [default = %d]\n",                   nGrowth );
    Abc_Print( -2, "\t-D <num>  :  the number of shared divisors to extract (-1: unlimited) [default = %d]\n",  nDivs );
    Abc_Print( -2, "\t-F <num>  :  the limit on the fanin count at a node [default = %d]\n",                    nFaninMax);
    Abc_Print( -2, "\t-L <num>  :  localization distances (0: unlimited) [default = %d]\n",                     nDist);
    Abc_Print( -2, "\t-R <num>  :  level constraint (0: unlimited, 1: preserve level) [default = %g]\n",        nLevelGrowRatio);
    Abc_Print( -2, "\t-M <num>  :  optimization target [default = %s]\n",                                       nMode ? "mapped" : "aig" );
    Abc_Print( -2, "\t-A <num>  :  mapper (0: amap, 1: &nf, 2: &simap) (experimental) [default = %d]\n",        nMappedMode );
    Abc_Print( -2, "\t-C <file> :  AIGER specifying external cares\n");
    Abc_Print( -2, "\t-S <num>  :  the random seed (0: random, >= 1: user defined) [default = %d]\n",           nSeed );
    Abc_Print( -2, "\t-T <num>  :  the timeout in seconds (0: unlimited) [default = %d]\n",                     nTimeOut );
    Abc_Print( -2, "\t-V <num>  :  the verbosity level [default = %d]\n",                                       nVerbose );
    Abc_Print( -2, "\t-c        :  check the equivalence [default = %s]\n",                                     fCheck ? "yes" : "no" );
    Abc_Print( -2, "\t-s        :  toggle accumulating structural choices [default = %s]\n",                    fChoices ? "yes" : "no" );
    Abc_Print( -2, "\t-d        :  toggle using \"dch\" before mapping [default = %s]\n",                       fDch ? "yes" : "no" );
    Abc_Print( -2, "\t-t        :  toggle timing-driven re-wiring [default = %s]\n",                            fTiming ? "yes" : "no" );
    Abc_Print( -2, "\t-h        :  prints the command usage\n" );
    Abc_Print( -2, "\n\tThis command was contributed by Jiun-Hao Chen from National Taiwan University.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9DeepSyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDeepSyn( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose );
    extern Gia_Man_t * Gia_ManDeepSyn2( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose );
    Gia_Man_t * pTemp; int c, nIters = 1, nNoImpr = ABC_INFINITY, TimeOut = 0, nAnds = 0, Seed = 0, fUseTwo = 0, fChoices = 0, fOpt = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IJTAStcovh" ) ) != EOF )
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
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            nNoImpr = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNoImpr < 0 )
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
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nAnds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nAnds < 0 )
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
        case 't':
            fUseTwo ^= 1;
            break;
        case 'c':
            fChoices ^= 1;
            break;
        case 'o':
            fOpt ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9DeepSyn(): There is no AIG.\n" );
        return 0;
    }
    if ( fOpt ) 
        pTemp = Gia_ManDeepSyn2( pAbc->pGia, nIters, nNoImpr, TimeOut, nAnds, Seed, fUseTwo, fChoices, fVerbose );
    else
        pTemp = Gia_ManDeepSyn( pAbc->pGia, nIters, nNoImpr, TimeOut, nAnds, Seed, fUseTwo, fChoices, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &deepsyn [-IJTAS <num>] [-tcovh]\n" );
    Abc_Print( -2, "\t           performs synthesis\n" );
    Abc_Print( -2, "\t-I <num> : the number of iterations [default = %d]\n",                   nIters  );
    Abc_Print( -2, "\t-J <num> : the number of steps without improvements [default = %d]\n",   nNoImpr  );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds (0 = no timeout) [default = %d]\n",    TimeOut );
    Abc_Print( -2, "\t-A <num> : the number of nodes to stop (0 = no limit) [default = %d]\n", nAnds   );
    Abc_Print( -2, "\t-S <num> : user-specified random seed (0 <= num <= 100) [default = %d]\n", Seed  );
    Abc_Print( -2, "\t-t       : toggle using two-input LUTs [default = %s]\n",                fUseTwo? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle computing structural choices [default = %s]\n",        fChoices? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggle using optimization [default = %s]\n",                  fOpt? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",       fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9RandSyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManRandSyn( Gia_Man_t * p, unsigned random_seed );
    Gia_Man_t * pTemp; int c, Seed = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Svh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "Abc_CommandAbc9RandSyn(): There is no AIG.\n" );
        return 0;
    }
    if ( Seed == 0 ) {
        Seed = Abc_Random(0) % 10000;
        printf( "Using random seed: %09u\n", Seed );
    }
    pTemp = Gia_ManRandSyn( pAbc->pGia, Seed );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &randsyn [-S <num>] [-vh]\n" );
    Abc_Print( -2, "\t           generates a random variation of the current AIG\n" );
    Abc_Print( -2, "\t-S <num> : user-specified random seed (0 <= num <= 100) [default = %d]\n", Seed  );
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
int Abc_CommandAbc9SatSyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManSyn( Gia_Man_t * p, int nNodes, int nOuts, int TimeOut, int fUseXor, int fFancy, int fVerbose );
    Gia_Man_t * pTemp; int c, nNodes = 0, nOuts = 0, TimeOut = 0, fUseXor = 0, fFancy = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NTafvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodes < 0 )
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
        case 'a':
            fUseXor ^= 1;
            break;
        case 'f':
            fFancy ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9SatSyn(): There is no AIG.\n" );
        return 0;
    }
    pTemp = Gia_ManSyn( pAbc->pGia, nNodes, nOuts, TimeOut, fUseXor, fFancy, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &satsyn [-NOT <num>] [-afvh]\n" );
    Abc_Print( -2, "\t           performs synthesis\n" );
    Abc_Print( -2, "\t-N <num> : the number of window nodes [default = %d]\n",                 nNodes  );
    Abc_Print( -2, "\t-O <num> : the number of window outputs [default = %d]\n",               nOuts  );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds (0 = no timeout) [default = %d]\n",    TimeOut );
    Abc_Print( -2, "\t-a       : toggle using xor-nodes [default = %s]\n",                     fUseXor? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggle using additional feature [default = %s]\n",            fFancy? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",       fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9StochSyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManStochSyn( int nSuppMax, int nMaxSize, int nIters, int TimeOut, int Seed, int fVerbose, char * pScript, int nProcs, int fDelayOpt, int fChoices );
    int c, nSuppMax = 0, nMaxSize = 1000, nIters = 10, TimeOut = 0, Seed = 0, nProcs = 1, fDelayOpt = 0, fChoices = 0, fVerbose = 0; char * pScript;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMITSPdcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSuppMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSuppMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
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
        case 'd':
            fDelayOpt ^= 1;
            break;
        case 'c':
            fChoices ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9StochSyn(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        printf( "Expecting a synthesis script in quotes on the command line (for example: \"&st; &dch; &if\").\n" );
        goto usage;
    }
    if ( fChoices && nIters < 2 )
    {
        printf( "The number of iterations should be more than 1.\n" );
        goto usage;
    }    
    pScript = Abc_UtilStrsav( argv[globalUtilOptind] );
    Gia_ManStochSyn( nSuppMax, nMaxSize, nIters, TimeOut, Seed, fVerbose, pScript, nProcs, fDelayOpt, fChoices );
    ABC_FREE( pScript );
    return 0;

usage:
    Abc_Print( -2, "usage: &stochsyn [-NMITSP <num>] [-dcvh] <script>\n" );
    Abc_Print( -2, "\t           performs stochastic synthesis using the given script\n" );
    Abc_Print( -2, "\t-N <num> : the max partition support size [default = %d]\n", nSuppMax );
    Abc_Print( -2, "\t-M <num> : the max partition size (in AIG nodes or LUTs) [default = %d]\n", nMaxSize );
    Abc_Print( -2, "\t-I <num> : the number of iterations [default = %d]\n",                   nIters  );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds (0 = no timeout) [default = %d]\n",    TimeOut );
    Abc_Print( -2, "\t-S <num> : user-specified random seed (0 <= num <= 100) [default = %d]\n", Seed  );
    Abc_Print( -2, "\t-P <num> : the number of concurrent processes (1 <= num <= 100) [default = %d]\n", nProcs );
    Abc_Print( -2, "\t-d       : toggle using delay-aware synthesis (if the script supports it) [default = %s]\n", fDelayOpt? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle computing structural choices [default = %s]\n",        fChoices? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",       fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<script> : synthesis script to use for each partition\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
