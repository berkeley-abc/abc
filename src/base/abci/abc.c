/**CFile****************************************************************

  FileName    [abc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Command file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "mainInt.h"
#include "fraig.h"
#include "fxu.h"
#include "cut.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandPrintStats   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintIo      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLatch   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFanio   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFactor  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLevel   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSupport ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSymms   ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandShowBdd      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowCut      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowAig      ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCollapse     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandStrash       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBalance      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRenode       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCleanup      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSweep        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFastExtract  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDisjoint     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandRewrite      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRefactor     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandLogic        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFrames       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSop          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBdd          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxes        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSat          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtSeqDcs    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneOutput    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneNode      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShortNames   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCut          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTest         ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFraig        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigTrust   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigStore   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigRestore ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigClean   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigSweep   ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandMap          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnmap        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAttach       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoice  ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFpga         ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandSeq          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRetime       ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCec          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSec          ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandDar          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDar          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDar          ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandSeqCleanup   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLcorr        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDSec         ( Abc_Frame_t * pAbc, int argc, char ** argv );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Printing",     "print_stats",   Abc_CommandPrintStats,       0 ); 
    Cmd_CommandAdd( pAbc, "Printing",     "print_io",      Abc_CommandPrintIo,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_latch",   Abc_CommandPrintLatch,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_fanio",   Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_factor",  Abc_CommandPrintFactor,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_level",   Abc_CommandPrintLevel,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_supp",    Abc_CommandPrintSupport,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_symm",    Abc_CommandPrintSymms,       0 );

    Cmd_CommandAdd( pAbc, "Printing",     "show_bdd",      Abc_CommandShowBdd,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_cut",      Abc_CommandShowCut,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_aig",      Abc_CommandShowAig,          0 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "collapse",      Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "strash",        Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "balance",       Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "renode",        Abc_CommandRenode,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cleanup",       Abc_CommandCleanup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "sweep",         Abc_CommandSweep,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fx",            Abc_CommandFastExtract,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "dsd",           Abc_CommandDisjoint,         1 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "rewrite",       Abc_CommandRewrite,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "refactor",      Abc_CommandRefactor,         1 );

    Cmd_CommandAdd( pAbc, "Various",      "logic",         Abc_CommandLogic,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "miter",         Abc_CommandMiter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "frames",        Abc_CommandFrames,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "sop",           Abc_CommandSop,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "bdd",           Abc_CommandBdd,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "muxes",         Abc_CommandMuxes,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "sat",           Abc_CommandSat,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "ext_seq_dcs",   Abc_CommandExtSeqDcs,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "one_output",    Abc_CommandOneOutput,        1 );
    Cmd_CommandAdd( pAbc, "Various",      "one_node",      Abc_CommandOneNode,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "short_names",   Abc_CommandShortNames,       0 );
    Cmd_CommandAdd( pAbc, "Various",      "cut",           Abc_CommandCut,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "test",          Abc_CommandTest,             0 );

    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig",         Abc_CommandFraig,            1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_trust",   Abc_CommandFraigTrust,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_store",   Abc_CommandFraigStore,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_restore", Abc_CommandFraigRestore,     1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_clean",   Abc_CommandFraigClean,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_sweep",   Abc_CommandFraigSweep,       1 );

    Cmd_CommandAdd( pAbc, "SC mapping",   "map",           Abc_CommandMap,              1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "unmap",         Abc_CommandUnmap,            1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "attach",        Abc_CommandAttach,           1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "sc",            Abc_CommandSuperChoice,      1 );

    Cmd_CommandAdd( pAbc, "FPGA mapping", "fpga",          Abc_CommandFpga,             1 );

    Cmd_CommandAdd( pAbc, "Sequential",   "seq",           Abc_CommandSeq,              1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "retime",        Abc_CommandRetime,           1 );

    Cmd_CommandAdd( pAbc, "Verification", "cec",           Abc_CommandCec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "sec",           Abc_CommandSec,              0 );

//    Rwt_Man4ExploreStart();
//    Map_Var3Print();
//    Map_Var4Test();

    Cmd_CommandAdd( pAbc, "Sequential",   "scleanup",      Abc_CommandSeqCleanup,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "lcorr",         Abc_CommandLcorr,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "ssweep",        Abc_CommandSeqSweep,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "dsec",          Abc_CommandDSec,             0 );
    {
        extern void Dar_LibStart();
        Dar_LibStart();
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_End()
{
    Abc_NtkFraigStoreClean();
//    Rwt_Man4ExplorePrint();
    {
        extern void Dar_LibStop();
        Dar_LibStop();
    }
    {
        extern void Cnf_ClearMemory();
        Cnf_ClearMemory();
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintStats( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    bool fShort;
    int c;
    int fFactor;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fShort  = 1;
    fFactor = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "sfh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShort ^= 1;
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
        fprintf( Abc_FrameReadErr(pAbc), "Empty network\n" );
        return 1;
    }
    Abc_NtkPrintStats( pOut, pNtk, fFactor );
    return 0;

usage:
    fprintf( pErr, "usage: print_stats [-fh]\n" );
    fprintf( pErr, "\t        prints the network statistics and\n" );
    fprintf( pErr, "\t-f    : toggles printing the literal count in the factored forms [default = %s]\n", fFactor? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintIo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( argc > util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == util_optind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
            return 1;
        }
        Abc_NodePrintFanio( pOut, pNode );
        return 0;
    }
    // print the nodes
    Abc_NtkPrintIo( pOut, pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_io [-h] <node>\n" );
    fprintf( pErr, "\t        prints the PIs/POs or fanins/fanouts of a node\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tnode  : the node to print fanins/fanouts\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintLatch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    // print the nodes
    Abc_NtkPrintLatch( pOut, pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_latch [-h]\n" );
    fprintf( pErr, "\t        prints information about latches\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintFanio( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // print the nodes
    Abc_NtkPrintFanio( pOut, pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_fanio [-h]\n" );
    fprintf( pErr, "\t        prints the statistics about fanins/fanouts of all nodes\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintFactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;
    int fUseRealNames;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseRealNames = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fUseRealNames ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        fprintf( pErr, "Printing factored forms can be done for SOP networks.\n" );
        return 1;
    }

    if ( argc > util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == util_optind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
            return 1;
        }
        Abc_NodePrintFactor( pOut, pNode, fUseRealNames );
        return 0;
    }
    // print the nodes
    Abc_NtkPrintFactor( pOut, pNtk, fUseRealNames );
    return 0;

usage:
    fprintf( pErr, "usage: print_factor [-nh] <node>\n" );
    fprintf( pErr, "\t        prints the factored forms of nodes\n" );
    fprintf( pErr, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tnode  : (optional) one node to consider\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintLevel( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;
    int fProfile;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fProfile = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'p':
            fProfile ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !fProfile && !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }

    if ( argc > util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == util_optind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
            return 1;
        }
        Abc_NodePrintLevel( pOut, pNode );
        return 0;
    }
    // process all COs
    Abc_NtkPrintLevel( pOut, pNtk, fProfile );
    return 0;

usage:
    fprintf( pErr, "usage: print_level [-ph] <node>\n" );
    fprintf( pErr, "\t        prints information about node level and cone size\n" );
    fprintf( pErr, "\t-p    : toggles printing level profile [default = %s]\n", fProfile? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tnode  : (optional) one node to consider\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSupport( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Vec_Ptr_t * vSuppFun;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;
    extern Vec_Ptr_t * Sim_ComputeFunSupp( Abc_Ntk_t * pNtk, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "vh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "This command works only for combinational networks.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    vSuppFun = Sim_ComputeFunSupp( pNtk, fVerbose );
    free( vSuppFun->pArray[0] );
    Vec_PtrFree( vSuppFun );
    return 0;

usage:
    fprintf( pErr, "usage: print_supp [-vh]\n" );
    fprintf( pErr, "\t        prints the supports of the CO nodes\n" );
    fprintf( pErr, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSymms( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fUseBdds;
    int fNaive;
    int fVerbose;
    extern void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseBdds = 0;
    fNaive   = 0;
    fVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "bnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fUseBdds ^= 1;
            break;
        case 'n':
            fNaive ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "This command works only for combinational networks.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: print_symm [-nbvh]\n" );
    fprintf( pErr, "\t         computes symmetries of the PO functions\n" );
    fprintf( pErr, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "bdd": "sat" );  
    fprintf( pErr, "\t-n     : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );  
    fprintf( pErr, "\t-v     : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShowBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;
    extern void Abc_NodeShowBdd( Abc_Obj_t * pNode );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Visualizing BDDs can only be done for logic BDD networks.\n" );
        return 1;
    }

    if ( argc != util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
    if ( pNode == NULL )
    {
        fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
        return 1;
    }
    Abc_NodeShowBdd( pNode );
    return 0;

usage:
    fprintf( pErr, "usage: show_bdd [-h] <node>\n" );
    fprintf( pErr, "       visualizes the BDD of a node using DOT and GSVIEW\n" );
#ifdef WIN32
    fprintf( pErr, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    fprintf( pErr, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    fprintf( pErr, "\tnode  : the node to consider\n");
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShowCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;
    int nNodeSizeMax;
    int nConeSizeMax;
    extern void Abc_NodeShowCut( Abc_Obj_t * pNode, int nNodeSizeMax, int nConeSizeMax );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = ABC_INFINITY;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "NCh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( nNodeSizeMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( nConeSizeMax < 0 ) 
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Visualizing cuts only works for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( argc != util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
    if ( pNode == NULL )
    {
        fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
        return 1;
    }
    Abc_NodeShowCut( pNode, nNodeSizeMax, nConeSizeMax );
    return 0;

usage:
    fprintf( pErr, "usage: show_cut [-N num] [-C num] [-h] <node>\n" );
    fprintf( pErr, "       visualizes the cut of a node using DOT and GSVIEW\n" );
#ifdef WIN32
    fprintf( pErr, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    fprintf( pErr, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    fprintf( pErr, "\t-N num : the max size of the cut to be computed [default = %d]\n", nNodeSizeMax );  
    fprintf( pErr, "\t-C num : the max support of the containing cone [default = %d]\n", nConeSizeMax );  
    fprintf( pErr, "\tnode   : the node to consider\n");
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShowAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern void Abc_NtkShowAig( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Visualizing AIG can only be done for AIGs (run \"strash\").\n" );
        return 1;
    }
    Abc_NtkShowAig( pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: show_aig [-h]\n" );
    fprintf( pErr, "       visualizes the AIG with choices using DOT and GSVIEW\n" );
#ifdef WIN32
    fprintf( pErr, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    fprintf( pErr, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCollapse( pNtk, 1 );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        pNtkRes = Abc_NtkCollapse( pNtk, 1 );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Collapsing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: collapse [-h]\n" );
    fprintf( pErr, "\t        collapses the network by constructing global BDDs\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fAllNodes;
    int fCleanup;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fAllNodes = 0;
    fCleanup  = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ach" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'c':
            fCleanup ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkStrash( pNtk, fAllNodes, fCleanup );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Strashing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: strash [-ach]\n" );
    fprintf( pErr, "\t        transforms combinational logic into an AIG\n" );
    fprintf( pErr, "\t-a    : toggles between using all nodes and DFS nodes [default = %s]\n", fAllNodes? "all": "DFS" );
    fprintf( pErr, "\t-c    : toggles cleanup to remove the dagling AIG nodes [default = %s]\n", fCleanup? "all": "DFS" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBalance( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
    {
        pNtkRes = Abc_NtkBalance( pNtk, fDuplicate );
    }
    else
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtkTemp == NULL )
        {
            fprintf( pErr, "Strashing before balancing has failed.\n" );
            return 1;
        }
        pNtkRes = Abc_NtkBalance( pNtkTemp, fDuplicate );
        Abc_NtkDelete( pNtkTemp );
    }

    // check if balancing worked
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Balancing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: balance [-dh]\n" );
    fprintf( pErr, "\t        transforms the current network into a well-balanced AIG\n" );
    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nThresh, nFaninMax, c;
    int fCnf;
    int fMulti;
    int fSimple;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nThresh   =  1;
    nFaninMax = 20;
    fCnf      =  0;
    fMulti    =  0;
    fSimple   =  0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "TFmcsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nThresh = atoi(argv[util_optind]);
            util_optind++;
            if ( nThresh < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[util_optind]);
            util_optind++;
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
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkRenode( pNtk, nThresh, nFaninMax, fCnf, fMulti, fSimple );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: renode [-T num] [-F num] [-cmsh]\n" );
    fprintf( pErr, "\t          transforms an AIG into a logic network by creating larger nodes\n" );
    fprintf( pErr, "\t-F num  : the maximum fanin size after renoding [default = %d]\n", nFaninMax );
    fprintf( pErr, "\t-T num  : the threshold for AIG node duplication [default = %d]\n", nThresh );
    fprintf( pErr, "\t          (an AIG node is the root of a new node after renoding\n" );
    fprintf( pErr, "\t          if doing so prevents duplication of more than %d AIG nodes,\n", nThresh );
    fprintf( pErr, "\t          that is, if [(numFanouts(Node)-1) * size(MFFC(Node))] > %d)\n", nThresh );
    fprintf( pErr, "\t-m      : creates multi-input AND graph [default = %s]\n", fMulti? "yes": "no" );
    fprintf( pErr, "\t-s      : creates a simple AIG (no renoding) [default = %s]\n", fSimple? "yes": "no" );
    fprintf( pErr, "\t-c      : performs renoding to derive the CNF [default = %s]\n", fCnf? "yes": "no" );
    fprintf( pErr, "\t-h      : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cleanup cannot be performed on the AIG.\n" );
        return 1;
    }
    // modify the current network
    Abc_NtkCleanup( pNtk, 0 );
    return 0;

usage:
    fprintf( pErr, "usage: cleanup [-h]\n" );
    fprintf( pErr, "\t        removes dangling nodes\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsSopLogic(pNtk) && !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Sweep cannot be performed on an AIG or a mapped network (unmap it first).\n" );
        return 1;
    }
    // modify the current network
    Abc_NtkSweep( pNtk, 0 );
    return 0;

usage:
    fprintf( pErr, "usage: sweep [-h]\n" );
    fprintf( pErr, "\t        removes dangling nodes; propagates constant, buffers, inverters\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk;
    FILE * pOut, * pErr;
    Fxu_Data_t * p = NULL;
    int c;
    extern bool Abc_NtkFastExtract( Abc_Ntk_t * pNtk, Fxu_Data_t * p );
    extern void Abc_NtkFxuFreeInfo( Fxu_Data_t * p );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // allocate the structure
    p = ALLOC( Fxu_Data_t, 1 );
    memset( p, 0, sizeof(Fxu_Data_t) );
    // set the defaults
    p->nPairsMax = 30000;
    p->nNodesExt = 10000;
    p->fOnlyS    = 0;
    p->fOnlyD    = 0;
    p->fUse0     = 0;
    p->fUseCompl = 1;
    p->fVerbose  = 0;
    util_getopt_reset();
    while ( (c = util_getopt(argc, argv, "LNsdzcvh")) != EOF ) 
    {
        switch (c) 
        {
            case 'L':
                if ( util_optind >= argc )
                {
                    fprintf( pErr, "Command line switch \"-L\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nPairsMax = atoi(argv[util_optind]);
                util_optind++;
                if ( p->nPairsMax < 0 ) 
                    goto usage;
                break;
            case 'N':
                if ( util_optind >= argc )
                {
                    fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nNodesExt = atoi(argv[util_optind]);
                util_optind++;
                if ( p->nNodesExt < 0 ) 
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
            case 'v':
                p->fVerbose ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }

    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        fprintf( pErr, "The network does not have internal nodes.\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Fast extract can only be applied to a logic network (run \"renode\").\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }


    // the nodes to be merged are linked into the special linked list
    Abc_NtkFastExtract( pNtk, p );
    Abc_NtkFxuFreeInfo( p );
    return 0;

usage:
    fprintf( pErr, "usage: fx [-N num] [-L num] [-sdzcvh]\n");
    fprintf( pErr, "\t         performs unate fast extract on the current network\n");
    fprintf( pErr, "\t-N num : the maximum number of divisors to extract [default = %d]\n", p->nNodesExt );  
    fprintf( pErr, "\t-L num : the maximum number of cube pairs to consider [default = %d]\n", p->nPairsMax );  
    fprintf( pErr, "\t-s     : use only single-cube divisors [default = %s]\n", p->fOnlyS? "yes": "no" );  
    fprintf( pErr, "\t-d     : use only double-cube divisors [default = %s]\n", p->fOnlyD? "yes": "no" );  
    fprintf( pErr, "\t-z     : use zero-weight divisors [default = %s]\n", p->fUse0? "yes": "no" );  
    fprintf( pErr, "\t-c     : use complement in the binary case [default = %s]\n", p->fUseCompl? "yes": "no" );  
    fprintf( pErr, "\t-v     : print verbose information [default = %s]\n", p->fVerbose? "yes": "no" ); 
    fprintf( pErr, "\t-h     : print the command usage\n");
    Abc_NtkFxuFreeInfo( p );
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkNew;
    int fGlobal, fRecursive, fVerbose, fPrint, fShort, c;

    extern Abc_Ntk_t * Abc_NtkDsdGlobal( Abc_Ntk_t * pNtk, bool fVerbose, bool fPrint, bool fShort );
    extern int         Abc_NtkDsdLocal( Abc_Ntk_t * pNtk, bool fVerbose, bool fRecursive );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fGlobal    = 1;
    fRecursive = 0;
    fVerbose   = 0;
    fPrint     = 0;
    fShort     = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "grvpsh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( fGlobal )
    {
//        fprintf( stdout, "Performing DSD of global functions of the network.\n" );
        // get the new network
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            pNtkNew = Abc_NtkStrash( pNtk, 0, 0 );
            pNtkRes = Abc_NtkDsdGlobal( pNtkNew, fVerbose, fPrint, fShort );
            Abc_NtkDelete( pNtkNew );
        }
        else
        {
            pNtkRes = Abc_NtkDsdGlobal( pNtk, fVerbose, fPrint, fShort );
        }
        if ( pNtkRes == NULL )
        {
            fprintf( pErr, "Global DSD has failed.\n" );
            return 1;
        }
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    else if ( fRecursive )
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            fprintf( pErr, "This command is only applicable to logic BDD networks.\n" );
            return 1;
        }
        fprintf( stdout, "Performing recursive DSD and MUX decomposition of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            fprintf( pErr, "Recursive DSD has failed.\n" );
    }
    else 
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            fprintf( pErr, "This command is only applicable to logic BDD networks.\n" );
            return 1;
        }
        fprintf( stdout, "Performing simple non-recursive DSD of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            fprintf( pErr, "Simple DSD of local functions has failed.\n" );
    }
    return 0;

usage:
    fprintf( pErr, "usage: dsd [-grvpsh]\n" );
    fprintf( pErr, "\t     decomposes the network using disjoint-support decomposition\n" );
    fprintf( pErr, "\t-g     : toggle DSD of global and local functions [default = %s]\n", fGlobal? "global": "local" );  
    fprintf( pErr, "\t-r     : toggle recursive DSD/MUX and simple DSD [default = %s]\n", fRecursive? "recursive DSD/MUX": "simple DSD" );  
    fprintf( pErr, "\t-v     : prints DSD statistics and runtime [default = %s]\n", fVerbose? "yes": "no" ); 
    fprintf( pErr, "\t-p     : prints DSD structure to the standard output [default = %s]\n", fPrint? "yes": "no" ); 
    fprintf( pErr, "\t-s     : use short PI names when printing DSD structure [default = %s]\n", fShort? "yes": "no" ); 
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    bool fPrecompute;
    bool fUseZeros;
    bool fVerbose;
    // external functions
    extern void   Rwr_Precompute();
    extern int    Abc_NtkRewrite( Abc_Ntk_t * pNtk, int fUseZeros, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fPrecompute = 0;
    fUseZeros   = 0;
    fVerbose    = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "xzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'x':
            fPrecompute ^= 1;
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

    if ( fPrecompute )
    {
        Rwr_Precompute();
        return 0;
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        fprintf( pErr, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRewrite( pNtk, fUseZeros, fVerbose ) )
    {
        fprintf( pErr, "Rewriting has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: rewrite [-zvh]\n" );
    fprintf( pErr, "\t         performs technology-independent rewriting of the AIG\n" );
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nNodeSizeMax;
    int nConeSizeMax;
    bool fUseZeros;
    bool fUseDcs;
    bool fVerbose;
    extern int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, bool fUseZeros, bool fUseDcs, bool fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = 16;
    fUseZeros    =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "NCzdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( nNodeSizeMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( nConeSizeMax < 0 ) 
                goto usage;
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

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        fprintf( pErr, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        fprintf( pErr, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRefactor( pNtk, nNodeSizeMax, nConeSizeMax, fUseZeros, fUseDcs, fVerbose ) )
    {
        fprintf( pErr, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: refactor [-N num] [-C num] [-zdvh]\n" );
    fprintf( pErr, "\t         performs technology-independent refactoring of the AIG\n" );
    fprintf( pErr, "\t-N num : the max support of the collapsed node [default = %d]\n", nNodeSizeMax );  
    fprintf( pErr, "\t-C num : the max support of the containing cone [default = %d]\n", nConeSizeMax );  
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    fprintf( pErr, "\t-d     : toggle using don't-cares [default = %s]\n", fUseDcs? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLogic( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsNetlist( pNtk ) )
    {
        fprintf( pErr, "This command is only applicable to netlists.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkNetlistToLogic( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Converting to a logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: logic [-h]\n" );
    fprintf( pErr, "\t        transforms a netlist into a logic network\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fCheck;
    int fComb;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fComb  = 1;
    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fComb ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + util_optind;
    nArgcNew = argc - util_optind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // compute the miter
    pNtkRes = Abc_NtkMiter( pNtk1, pNtk2, fComb );
    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );

    // get the new network
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Miter computation has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: miter [-ch] <file1> <file2>\n" );
    fprintf( pErr, "\t        computes the miter of the two circuits\n" );
    fprintf( pErr, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tfile1 : (optional) the file with the first network\n");
    fprintf( pErr, "\tfile2 : (optional) the file with the second network\n");
    fprintf( pErr, "\t        if no files are given, uses the current network and its spec\n");
    fprintf( pErr, "\t        if one file is given, uses the current network and the file\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp, * pNtkRes;
    int fInitial;
    int nFrames;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fInitial = 0;
    nFrames  = 5;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "Fih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[util_optind]);
            util_optind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'i':
            fInitial ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0 );
        pNtkRes  = Abc_NtkFrames( pNtkTemp, nFrames, fInitial );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes  = Abc_NtkFrames( pNtk, nFrames, fInitial );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Unrolling the network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: frames [-F num] [-ih]\n" );
    fprintf( pErr, "\t         unrolls the network for a number of time frames\n" );
    fprintf( pErr, "\t-F num : the number of frames to unroll [default = %d]\n", nFrames );
    fprintf( pErr, "\t-i     : toggles initializing the first frame [default = %s]\n", fInitial? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Converting to SOP is possible when node functions are BDDs.\n" );
        return 1;
    }
    if ( !Abc_NtkBddToSop( pNtk ) )
    {
        fprintf( pErr, "Converting to SOP has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: sop [-h]\n" );
    fprintf( pErr, "\t         converts node functions from BDD to SOP\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        fprintf( pErr, "Converting to BDD is possible when node functions are SOPs.\n" );
        return 1;
    }
    if ( !Abc_NtkSopToBdd( pNtk ) )
    {
        fprintf( pErr, "Converting to BDD has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: bdd [-h]\n" );
    fprintf( pErr, "\t         converts node functions from SOP to BDD\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Only a BDD logic network can be converted to MUXes.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkBddToMuxes( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Converting to MUXes has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: muxes [-h]\n" );
    fprintf( pErr, "\t        converts the current network by a network derived by\n" );
    fprintf( pErr, "\t        replacing all nodes by DAGs isomorphic to the local BDDs\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "vh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( stdout, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( stdout, "This command can only be applied to logic network (run \"renode -c\").\n" );
        return 0;
    }
    if ( Abc_NtkIsMappedLogic(pNtk) )
        Abc_NtkUnmap(pNtk);
    if ( Abc_NtkIsSopLogic(pNtk) )
        Abc_NtkSopToBdd(pNtk);

    if ( Abc_NtkMiterSat( pNtk, fVerbose ) )
        printf( "The miter is satisfiable.\n" );
    else
        printf( "The miter is unsatisfiable.\n" );
    return 0;

usage:
    fprintf( pErr, "usage: sat [-vh]\n" );
    fprintf( pErr, "\t         solves the miter\n" );
    fprintf( pErr, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExtSeqDcs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;
    extern int Abc_NtkExtractSequentialDcs( Abc_Ntk_t * pNet, bool fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "vh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        fprintf( stdout, "The current network has no latches.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( stdout, "This command works only for AIGs (run \"strash\").\n" );
        return 0;
    }
    if ( !Abc_NtkExtractSequentialDcs( pNtk, fVerbose ) )
    {
        fprintf( stdout, "Extracting sequential don't-cares has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: ext_seq_dcs [-vh]\n" );
    fprintf( pErr, "\t         create EXDC network using unreachable states\n" );
    fprintf( pErr, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOneOutput( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode;
    int c;
    int fUseAllCis;
    int Output;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseAllCis = 0;
    Output = -1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "Oah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            Output = atoi(argv[util_optind]);
            util_optind++;
            if ( Output < 0 ) 
                goto usage;
            break;
        case 'a':
            fUseAllCis ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Currently can only be applied to the logic network or an AIG.\n" );
        return 1;
    }

    if ( argc > util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == util_optind + 1 )
    {
        pNode = Abc_NtkFindCo( pNtk, argv[util_optind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find CO node \"%s\".\n", argv[util_optind] );
            return 1;
        }
        pNtkRes = Abc_NtkSplitOutput( pNtk, pNode, fUseAllCis );
    }
    else
    {
        if ( Output == -1 )
        {
            fprintf( pErr, "The output is not specified.\n" );
            return 1;
        }
        if ( Output >= Abc_NtkCoNum(pNtk) )
        {
            fprintf( pErr, "The 0-based output number (%d) is larger than the number of outputs (%d).\n", Output, Abc_NtkCoNum(pNtk) );
            return 1;
        }
        pNtkRes = Abc_NtkSplitOutput( pNtk, Abc_NtkCo(pNtk,Output), fUseAllCis );
    }
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Splitting one output has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: one_output [-O num] [-ah] <name>\n" );
    fprintf( pErr, "\t         replaces the current network by the logic cone of one output\n" );
    fprintf( pErr, "\t-a     : toggle writing all CIs or structral support only [default = %s]\n", fUseAllCis? "all": "structural" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t-O num : (optional) the 0-based number of the output\n");
    fprintf( pErr, "\tname   : (optional) the name of the output\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOneNode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Currently can only be applied to a logic network.\n" );
        return 1;
    }

    if ( argc != util_optind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[util_optind] );
    if ( pNode == NULL )
    {
        fprintf( pErr, "Cannot find node \"%s\".\n", argv[util_optind] );
        return 1;
    }

    pNtkRes = Abc_NtkSplitNode( pNtk, pNode );
//    pNtkRes = Abc_NtkDeriveFromBdd( pNtk->pManFunc, pNode->pData, NULL, NULL );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Splitting one node has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: one_node [-h] <name>\n" );
    fprintf( pErr, "\t         replaces the current network by the network composed of one node\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\tname   : the node name\n");
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShortNames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    Abc_NtkShortNames( pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: short_names [-h]\n" );
    fprintf( pErr, "\t         replaces PI/PO/latch names by short char strings\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    pParams->nVarsMax  = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 250;   // the max number of cuts kept at a node
    pParams->fTruth    = 1;     // compute truth tables
    pParams->fHash     = 0;     // hash cuts to detect unique
    pParams->fFilter   = 0;     // filter dominated cuts
    pParams->fSeq      = 0;     // compute sequential cuts
    pParams->fDrop     = 0;     // drop cuts on the fly
    pParams->fVerbose  = 0;     // the verbosiness flag
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "KMtrfsdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nVarsMax = atoi(argv[util_optind]);
            util_optind++;
            if ( pParams->nVarsMax < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nKeepMax = atoi(argv[util_optind]);
            util_optind++;
            if ( pParams->nKeepMax < 0 ) 
                goto usage;
            break;
        case 't':
            pParams->fTruth ^= 1;
            break;
        case 'r':
            pParams->fHash ^= 1;
            break;
        case 'f':
            pParams->fFilter ^= 1;
            break;
        case 's':
            pParams->fSeq ^= 1;
            break;
        case 'd':
            pParams->fDrop ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cut computation is available only for AIGs (run \"strash\").\n" );
        return 1;
    }
    pCutMan = Abc_NtkCuts( pNtk, pParams );
    Cut_ManPrintStats( pCutMan );
    Cut_ManStop( pCutMan );
    return 0;

usage:
    fprintf( pErr, "usage: cut [-K num] [-M num] [-trfsdvh]\n" );
    fprintf( pErr, "\t         computes k-feasible cuts for the AIG\n" );
    fprintf( pErr, "\t-K num : max number of leaves (4 <= num <= 6) [default = %d]\n",    pParams->nVarsMax );
    fprintf( pErr, "\t-M num : max number of cuts stored at a node [default = %d]\n",     pParams->nKeepMax );
    fprintf( pErr, "\t-t     : toggle truth table computation [default = %s]\n",          pParams->fTruth? "yes": "no" );
    fprintf( pErr, "\t-r     : toggle reduction by hashing [default = %s]\n",             pParams->fHash? "yes": "no" );
    fprintf( pErr, "\t-f     : toggle filtering by dominance [default = %s]\n",           pParams->fFilter? "yes": "no" );
    fprintf( pErr, "\t-s     : toggle sequential cut computation [default = %s]\n",       pParams->fSeq? "yes": "no" );
    fprintf( pErr, "\t-d     : toggle dropping when fanouts are done [default = %s]\n",   pParams->fDrop? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n",     pParams->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    // run the command
    pNtkRes = Abc_NtkMiterForCofactors( pNtk, 0, 0, -1 );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: test [-h]\n" );
    fprintf( pErr, "\t         testbench for new procedures\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fAllNodes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fAllNodes = 0;
    pParams->nPatsRand  = 2048; // the number of words of random simulation info
    pParams->nPatsDyna  = 2048; // the number of words of dynamic simulation info
    pParams->nBTLimit   = 99;   // the max number of backtracks to perform
    pParams->fFuncRed   =  1;   // performs only one level hashing
    pParams->fFeedBack  =  1;   // enables solver feedback
    pParams->fDist1Pats =  1;   // enables distance-1 patterns
    pParams->fDoSparse  =  0;   // performs equiv tests for sparse functions 
    pParams->fChoicing  =  0;   // enables recording structural choices
    pParams->fTryProve  =  0;   // tries to solve the final miter
    pParams->fVerbose   =  0;   // the verbosiness flag
    pParams->fVerboseP  =  0;   // the verbosiness flag
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "RDBrscpvah" ) ) != EOF )
    {
        switch ( c )
        {

        case 'R':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsRand = atoi(argv[util_optind]);
            util_optind++;
            if ( pParams->nPatsRand < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsDyna = atoi(argv[util_optind]);
            util_optind++;
            if ( pParams->nPatsDyna < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nBTLimit = atoi(argv[util_optind]);
            util_optind++;
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
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    } 

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Can only fraig a logic network or an AIG.\n" );
        return 1;
    }

    // report the proof
    pParams->fVerboseP = pParams->fTryProve;

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes );
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Fraiging has failed.\n" );
        return 1;
    }

    if ( pParams->fTryProve ) // report the result
        Abc_NtkMiterReport( pNtkRes );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    sprintf( Buffer, "%d", pParams->nBTLimit );
    fprintf( pErr, "usage: fraig [-R num] [-D num] [-B num] [-rscpvah]\n" );
    fprintf( pErr, "\t         transforms a logic network into a functionally reduced AIG\n" );
    fprintf( pErr, "\t-R num : number of random patterns (127 < num < 32769) [default = %d]\n",     pParams->nPatsRand );
    fprintf( pErr, "\t-D num : number of systematic patterns (127 < num < 32769) [default = %d]\n", pParams->nPatsDyna );
    fprintf( pErr, "\t-B num : number of backtracks for one SAT problem [default = %s]\n",    pParams->nBTLimit==-1? "infinity" : Buffer );
    fprintf( pErr, "\t-r     : toggle functional reduction [default = %s]\n",                 pParams->fFuncRed? "yes": "no" );
    fprintf( pErr, "\t-s     : toggle considering sparse functions [default = %s]\n",         pParams->fDoSparse? "yes": "no" );
    fprintf( pErr, "\t-c     : toggle accumulation of choices [default = %s]\n",              pParams->fChoicing? "yes": "no" );
    fprintf( pErr, "\t-p     : toggle proving the final miter [default = %s]\n",              pParams->fTryProve? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n",                       pParams->fVerbose?  "yes": "no" );
    fprintf( pErr, "\t-a     : toggle between all nodes and DFS nodes [default = %s]\n",      fAllNodes? "all": "dfs" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkFraigTrust( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Fraiging in the trust mode has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: fraig_trust [-h]\n" );
    fprintf( pErr, "\t        transforms the current network into an AIG assuming it is FRAIG with choices\n" );
//    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkFraigStore( pNtk ) )
    {
        fprintf( pErr, "Fraig storing has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: fraig_store [-h]\n" );
    fprintf( pErr, "\t        saves the current network in the AIG database\n" );
//    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dh" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkFraigRestore();
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Fraig restoring has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: fraig_restore [-h]\n" );
    fprintf( pErr, "\t        makes the current network by fraiging the AIG database\n" );
//    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dh" ) ) != EOF )
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
    fprintf( pErr, "usage: fraig_clean [-h]\n" );
    fprintf( pErr, "\t        cleans the internal FRAIG storage\n" );
//    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fUseInv;
    int fVerbose;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseInv   = 1;
    fVerbose  = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fUseInv ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cannot sweep AIGs (use \"fraig\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Transform the current network into a logic network.\n" );
        return 1;
    }
    // modify the current network
    if ( !Abc_NtkFraigSweep( pNtk, fUseInv, fVerbose ) )
    {
        fprintf( pErr, "Sweeping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: fraig_sweep [-vh]\n" );
    fprintf( pErr, "\t        performs technology-dependent sweep\n" );
//    fprintf( pErr, "\t-i    : toggle using inverter for complemented nodes [default = %s]\n", fUseInv? "yes": "no" );
    fprintf( pErr, "\t-v    : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    char Buffer[100];
    double DelayTarget;
    int fRecovery;
    int fSweep;
    int fSwitching;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkMap( Abc_Ntk_t * pNtk, double DelayTarget, int fRecovery, int fSwitching, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    DelayTarget =-1;
    fRecovery   = 1;
    fSweep      = 1;
    fSwitching  = 0;
    fVerbose    = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "Daspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[util_optind]);
            util_optind++;
            if ( DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'a':
            fRecovery ^= 1;
            break;
        case 's':
            fSweep ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Strashing before mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Balancing before mapping has failed.\n" );
            return 1;
        }
        fprintf( pOut, "The network was strashed and balanced before mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            fprintf( pErr, "Mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            fprintf( pErr, "Mapping has failed.\n" );
            return 1;
        }
    }

    if ( fSweep )
        Abc_NtkFraigSweep( pNtkRes, 0, 0 );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "not used" );
    else
        sprintf( Buffer, "%.3f", DelayTarget );
    fprintf( pErr, "usage: map [-D num] [-aspvh]\n" );
    fprintf( pErr, "\t         performs standard cell mapping of the current network\n" );
    fprintf( pErr, "\t-D num : sets the global required times [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-a     : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    fprintf( pErr, "\t-s     : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    fprintf( pErr, "\t-p     : optimizes power by minimizing switching activity [default = %s]\n", fSwitching? "yes": "no" );
    fprintf( pErr, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern int Abc_NtkUnmap( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(pNtk) )
    {
        fprintf( pErr, "Cannot unmap the network that is not mapped.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkUnmap( pNtk ) )
    {
        fprintf( pErr, "Unmapping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: unmap [-h]\n" );
    fprintf( pErr, "\t        replaces the library gates by the logic nodes represented using SOPs\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern int Abc_NtkUnmap( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        fprintf( pErr, "Can only attach gates if the nodes have SOP representations.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkAttach( pNtk ) )
    {
        fprintf( pErr, "Attaching gates has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: attach [-h]\n" );
    fprintf( pErr, "\t        replaces the SOP functions by the gates from the library\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkSuperChoice( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkSuperChoice( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: sc [-h]\n" );
    fprintf( pErr, "\t      performs superchoicing\n" );
    fprintf( pErr, "\t      (accumulate: \"r file.blif; rsup; b; sc; f -ac; wb file_sc.blif\")\n" );
    fprintf( pErr, "\t      (map without supergate library: \"r file_sc.blif; ft; map\")\n" );
    fprintf( pErr, "\t-h  : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fSwitching;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkFpga( Abc_Ntk_t * pNtk, int fRecovery, int fSwitching, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fRecovery  = 1;
    fSwitching = 0;
    fVerbose   = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "apvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fRecovery ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        fprintf( pOut, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            fprintf( pErr, "FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            fprintf( pErr, "FPGA mapping has failed.\n" );
            return 1;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: fpga [-apvh]\n" );
    fprintf( pErr, "\t        performs FPGA mapping of the current network\n" );
    fprintf( pErr, "\t-a    : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    fprintf( pErr, "\t-p    : optimizes power by minimizing switching activity [default = %s]\n", fSwitching? "yes": "no" );
    fprintf( pErr, "\t-v    : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h    : prints the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkSuperChoice( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    printf( "This command is not yet implemented.\n" );
    return 0;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Works only for AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkAigToSeq( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Converting to sequential AIG has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: seq [-h]\n" );
    fprintf( pErr, "\t        converts AIG into sequential AIG (while sweeping latches)\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fForward;
    int fBackward;

    extern Abc_Ntk_t * Abc_NtkSuperChoice( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fForward = 0;
    fBackward = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "fbh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fForward ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    printf( "This command is not yet implemented.\n" );
    return 0;


    if ( !Abc_NtkIsSeq(pNtk) )
    {
        fprintf( pErr, "Works only for sequential AIG.\n" );
        return 1;
    }

    // get the new network
    if ( fForward )
        Abc_NtkSeqRetimeForward( pNtk );
    else if ( fBackward )
        Abc_NtkSeqRetimeBackward( pNtk );
    else
        Abc_NtkSeqRetimeDelay( pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: retime [-fbh]\n" );
    fprintf( pErr, "\t        retimes sequential AIG (default is Pan's algorithm)\n" );
    fprintf( pErr, "\t-f    : toggle forward retiming [default = %s]\n", fForward? "yes": "no" );
    fprintf( pErr, "\t-b    : toggle backward retiming [default = %s]\n", fBackward? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;

    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
    extern void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fVerbose );


    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fSat     = 0;
    fVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSat ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + util_optind;
    nArgcNew = argc - util_optind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // perform equivalence checking
    if ( fSat )
        Abc_NtkCecSat( pNtk1, pNtk2 );
    else
        Abc_NtkCecFraig( pNtk1, pNtk2, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: cec [-svh] <file1> <file2>\n" );
    fprintf( pErr, "\t        performs combinational equivalence checking\n" );
    fprintf( pErr, "\t-s    : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    fprintf( pErr, "\t-v    : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tfile1 : (optional) the file with the first network\n");
    fprintf( pErr, "\tfile2 : (optional) the file with the second network\n");
    fprintf( pErr, "\t        if no files are given, uses the current network and its spec\n");
    fprintf( pErr, "\t        if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int nFrames;

    extern void Abc_NtkSecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames );
    extern void Abc_NtkSecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames );


    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames = 3;
    fSat    = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "Fsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[util_optind]);
            util_optind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 's':
            fSat ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + util_optind;
    nArgcNew = argc - util_optind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // perform equivalence checking
    if ( fSat )
        Abc_NtkSecSat( pNtk1, pNtk2, nFrames );
    else
        Abc_NtkSecFraig( pNtk1, pNtk2, nFrames );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: sec [-sh] [-F num] <file1> <file2>\n" );
    fprintf( pErr, "\t         performs bounded sequential equivalence checking\n" );
    fprintf( pErr, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t-F num : the number of time frames to use [default = %d]\n", nFrames );
    fprintf( pErr, "\tfile1  : (optional) the file with the first network\n");
    fprintf( pErr, "\tfile2  : (optional) the file with the second network\n");
    fprintf( pErr, "\t         if no files are given, uses the current network and its spec\n");
    fprintf( pErr, "\t         if one file is given, uses the current network and the file\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fLatchSweep;
    int fAutoSweep;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchSweep, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDar( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fLatchSweep = 0;
    fAutoSweep  = 0;
    fVerbose    = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "lavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fLatchSweep ^= 1;
            break;
        case 'a':
            fAutoSweep ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Only works for structrally hashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        fprintf( pErr, "Only works for sequential networks.\n" );
        return 1;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarLatchSweep( pNtk, fLatchSweep, fVerbose );
//    pNtkRes = Abc_NtkDar( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Sequential cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: scleanup [-lvh]\n" );
    fprintf( pErr, "\t         performs sequential cleanup\n" );
    fprintf( pErr, "\t         - removes nodes/latches that do not feed into POs\n" );
    fprintf( pErr, "\t         - removes stuck-at and identical latches (latch sweep)\n" );
//    fprintf( pErr, "\t         - replaces autonomous logic by free PI variables\n" );
    fprintf( pErr, "\t-l     : toggle sweeping latches [default = %s]\n", fLatchSweep? "yes": "no" );
//    fprintf( pErr, "\t-a     : toggle removing autonomous logic [default = %s]\n", fAutoSweep? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFramesP;
    int nConfMax;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDarLcorr( Abc_Ntk_t * pNtk, int nFramesP, int nConfMax, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFramesP   = 0;
    nConfMax   = 10000;
    fVerbose   = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "PCvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesP = atoi(argv[util_optind]);
            util_optind++;
            if ( nFramesP < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[util_optind]);
            util_optind++;
            if ( nConfMax < 0 ) 
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        printf( "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDarLcorr( pNtk, nFramesP, nConfMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: lcorr [-P num] [-C num] [-vh]\n" );
    fprintf( pErr, "\t         computes latch correspondence using 1-step induction\n" );
    fprintf( pErr, "\t-P num : number of time frames to use as the prefix [default = %d]\n", nFramesP );
    fprintf( pErr, "\t-C num : max conflict number when proving latch equivalence [default = %d]\n", nConfMax );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFramesP;
    int nFramesK;
    int nMaxImps;
    int nMaxLevs;
    int fUseImps;
    int fRewrite;
    int fLatchCorr;
    int fWriteImps;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, int nFramesP, int nFrames, int nMaxImps, int nMaxLevs, int fRewrite, int fUseImps, int fLatchCorr, int fWriteImps, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFramesP   = 0;
    nFramesK   = 1;
    nMaxImps   = 5000;
    nMaxLevs   = 0;
    fUseImps   = 0;
    fRewrite   = 0;
    fLatchCorr = 0;
    fWriteImps = 0;
    fVerbose   = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "PFILirlevh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesP = atoi(argv[util_optind]);
            util_optind++;
            if ( nFramesP < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesK = atoi(argv[util_optind]);
            util_optind++;
            if ( nFramesK <= 0 ) 
                goto usage;
            break;
        case 'I':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxImps = atoi(argv[util_optind]);
            util_optind++;
            if ( nMaxImps <= 0 ) 
                goto usage;
            break;
        case 'L':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxLevs = atoi(argv[util_optind]);
            util_optind++;
            if ( nMaxLevs <= 0 ) 
                goto usage;
            break;
        case 'i':
            fUseImps ^= 1;
            break;
        case 'r':
            fRewrite ^= 1;
            break;
        case 'l':
            fLatchCorr ^= 1;
            break;
        case 'e':
            fWriteImps ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        printf( "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDarSeqSweep( pNtk, nFramesP, nFramesK, nMaxImps, nMaxLevs, fRewrite, fUseImps, fLatchCorr, fWriteImps, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: ssweep [-P num] [-F num] [-lrevh]\n" );
    fprintf( pErr, "\t         performs sequential sweep using K-step induction\n" );
    fprintf( pErr, "\t-P num : number of time frames to use as the prefix [default = %d]\n", nFramesP );
    fprintf( pErr, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", nFramesK );
//    fprintf( pErr, "\t-I num : max number of implications to consider [default = %d]\n", nMaxImps );
    fprintf( pErr, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", nMaxLevs );
//    fprintf( pErr, "\t-i     : toggle using implications [default = %s]\n", fUseImps? "yes": "no" );
    fprintf( pErr, "\t-l     : toggle latch correspondence only [default = %s]\n", fLatchCorr? "yes": "no" );
    fprintf( pErr, "\t-r     : toggle AIG rewriting [default = %s]\n", fRewrite? "yes": "no" );
    fprintf( pErr, "\t-e     : toggle writing implications as assertions [default = %s]\n", fWriteImps? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fRetimeFirst;
    int fVerbose;
    int fVeryVerbose;
    int nFrames;

    extern int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fRetimeFirst, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames      =16;
    fRetimeFirst = 1;
    fVerbose     = 0;
    fVeryVerbose = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "Krwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[util_optind]);
            util_optind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'r':
            fRetimeFirst ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + util_optind;
    nArgcNew = argc - util_optind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
    {
        printf( "The network has no latches. Used combinational command \"cec\".\n" );
        return 0;
    }

    // perform verification
    Abc_NtkDarSec( pNtk1, pNtk2, nFrames, fRetimeFirst, fVerbose, fVeryVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: dsec [-K num] [-rwvh] <file1> <file2>\n" );
    fprintf( pErr, "\t         performs inductive sequential equivalence checking\n" );
    fprintf( pErr, "\t-K num : the limit on the depth of induction [default = %d]\n", nFrames );
    fprintf( pErr, "\t-r     : toggles forward retiming at the beginning [default = %s]\n", fRetimeFirst? "yes": "no" );
    fprintf( pErr, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-w     : toggles additional verbose output [default = %s]\n", fVeryVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\tfile1  : (optional) the file with the first network\n");
    fprintf( pErr, "\tfile2  : (optional) the file with the second network\n");
    fprintf( pErr, "\t         if no files are given, uses the current network and its spec\n");
    fprintf( pErr, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


