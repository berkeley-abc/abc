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
#include "ft.h"
#include "fraig.h"
#include "fxu.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandPrintStats   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintIo      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFanio   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFactor  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowBdd      ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCollapse     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandStrash       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBalance      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRenode       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCleanup      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFastExtract  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDisjoint     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRes          ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandLogic        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFrames       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSop          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBdd          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSat          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtSeqDcs    ( Abc_Frame_t * pAbc, int argc, char ** argv );

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

static int Abc_CommandCec          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSec          ( Abc_Frame_t * pAbc, int argc, char ** argv );

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
    Cmd_CommandAdd( pAbc, "Printing",     "print_fanio",   Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_factor",  Abc_CommandPrintFactor,      0 );

    Cmd_CommandAdd( pAbc, "Printing",     "show_bdd",      Abc_CommandShowBdd,          0 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "collapse",      Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "strash",        Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "balance",       Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "renode",        Abc_CommandRenode,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cleanup",       Abc_CommandCleanup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fx",            Abc_CommandFastExtract,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "dsd",           Abc_CommandDisjoint,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "res",           Abc_CommandRes,              1 );

    Cmd_CommandAdd( pAbc, "Various",      "logic",         Abc_CommandLogic,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "miter",         Abc_CommandMiter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "frames",        Abc_CommandFrames,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "sop",           Abc_CommandSop,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "bdd",           Abc_CommandBdd,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "sat",           Abc_CommandSat,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "ext_seq_dcs",   Abc_CommandExtSeqDcs,        0 );

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

    Cmd_CommandAdd( pAbc, "Verification", "cec",           Abc_CommandCec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "sec",           Abc_CommandSec,              0 );

    Ft_FactorStartMan();
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_End()
{
    Ft_FactorStopMan();
    Abc_NtkFraigStoreClean();
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

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fShort = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShort ^= 1;
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
    Abc_NtkPrintStats( pOut, pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_stats [-h]\n" );
    fprintf( pErr, "\t        prints the network statistics and\n" );
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
    fprintf( pErr, "usage: print_io [-h]\n" );
    fprintf( pErr, "\t        prints the PIs/POs or fanins/fanouts of a node\n" );
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

    if ( !Abc_NtkIsNetlist(pNtk) && !Abc_NtkIsLogicSop(pNtk) )
    {
        fprintf( pErr, "Printing factored forms can be done for netlist and SOP networks.\n" );
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
//        Ft_FactorStartMan();
        Abc_NodePrintFactor( pOut, pNode );
//        Ft_FactorStopMan();
        return 0;
    }
    // print the nodes
//    Ft_FactorStartMan();
    Abc_NtkPrintFactor( pOut, pNtk );
//    Ft_FactorStopMan();
    return 0;

usage:
    fprintf( pErr, "usage: print_factor [-h] <node>\n" );
    fprintf( pErr, "\t        prints the factored forms of nodes\n" );
    fprintf( pErr, "\tnode  : (optional) one node to consider\n");
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    extern void Abc_NodePrintBdd( Abc_Obj_t * pNode );

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

    if ( !Abc_NtkIsLogicBdd(pNtk) )
    {
        fprintf( pErr, "Printing BDDs can only be done for logic BDD networks.\n" );
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
    Abc_NodePrintBdd( pNode );
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

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Can only collapse a logic network.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsAig(pNtk) )
        pNtkRes = Abc_NtkCollapse( pNtk, 1 );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0 );
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

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fAllNodes = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
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

    // get the new network
    pNtkRes = Abc_NtkStrash( pNtk, fAllNodes );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Strashing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: strash [-ah]\n" );
    fprintf( pErr, "\t        transforms combinational logic into an AIG\n" );
    fprintf( pErr, "\t-a    : toggles between using all nodes and DFS nodes [default = %s]\n", fAllNodes? "all": "DFS" );
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
    if ( !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Cannot balance a network that is not an AIG.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkBalance( pNtk, fDuplicate );
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
    fprintf( pErr, "\t        transforms an AIG into a well-balanced AIG\n" );
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
    nThresh   =  0;
    nFaninMax = 20;
    fCnf      =  0;
    fMulti    =  0;
    fSimple   =  0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "tfmcsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 't':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-t\" should be followed by an integer.\n" );
                goto usage;
            }
            nThresh = atoi(argv[util_optind]);
            util_optind++;
            if ( nThresh < 0 ) 
                goto usage;
            break;
        case 'f':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-f\" should be followed by an integer.\n" );
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
    if ( !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Cannot renode a network that is not an AIG.\n" );
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
    fprintf( pErr, "usage: renode [-t num] [-f num] [-cmsh]\n" );
    fprintf( pErr, "\t          transforms an AIG into a logic network by creating larger nodes\n" );
    fprintf( pErr, "\t-t num  : the threshold for AIG node duplication [default = %d]\n", nThresh );
    fprintf( pErr, "\t-f num  : the maximum fanin size after renoding [default = %d]\n", nFaninMax );
    fprintf( pErr, "\t-c      : performs renoding to derive the CNF [default = %s]\n", fCnf? "yes": "no" );
    fprintf( pErr, "\t-m      : creates multi-input AND graph [default = %s]\n", fMulti? "yes": "no" );
    fprintf( pErr, "\t-s      : creates a simple AIG (no renoding) [default = %s]\n", fSimple? "yes": "no" );
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

    // modify the current network
    Abc_NtkCleanup( pNtk, 0 );
    return 0;

usage:
    fprintf( pErr, "usage: cleanup [-h]\n" );
    fprintf( pErr, "\t        removes dangling nodes\n" );
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
    while ( (c = util_getopt(argc, argv, "lnsdzcvh")) != EOF ) 
    {
        switch (c) 
        {
            case 'l':
                if ( util_optind >= argc )
                {
                    fprintf( pErr, "Command line switch \"-l\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nPairsMax = atoi(argv[util_optind]);
                util_optind++;
                if ( p->nPairsMax < 0 ) 
                    goto usage;
                break;
            case 'n':
                if ( util_optind >= argc )
                {
                    fprintf( pErr, "Command line switch \"-n\" should be followed by an integer.\n" );
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

    // the nodes to be merged are linked into the special linked list
    Abc_NtkFastExtract( pNtk, p );
    Abc_NtkFxuFreeInfo( p );
    return 0;

usage:
    fprintf( pErr, "usage: fx [-n num] [-l num] [-sdzcvh]\n");
    fprintf( pErr, "\t         performs unate fast extract on the current network\n");
    fprintf( pErr, "\t-n num : the maximum number of divisors to extract [default = %d]\n", p->nNodesExt );  
    fprintf( pErr, "\t-l num : the maximum number of cube pairs to consider [default = %d]\n", p->nPairsMax );  
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
    extern int         Abc_NtkDsdRecursive( Abc_Ntk_t * pNtk, bool fVerbose );

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

    if ( !fGlobal && !fRecursive )
    {
        fprintf( pErr, "Decomposition should be either global or recursive.\n" );
        return 1;
    }

    if ( fGlobal )
    {
        // get the new network
        if ( !Abc_NtkIsAig(pNtk) )
        {
            pNtkNew = Abc_NtkStrash( pNtk, 0 );
            pNtkRes = Abc_NtkDsdGlobal( pNtkNew, fVerbose, fPrint, fShort );
            Abc_NtkDelete( pNtkNew );
        }
        else
        {
            pNtkRes = Abc_NtkDsdGlobal( pNtk, fVerbose, fPrint, fShort );
        }
        if ( pNtkRes == NULL )
        {
            fprintf( pErr, "Global disjoint support decomposition has failed.\n" );
            return 1;
        }
        if ( fRecursive )
        {
            if ( !Abc_NtkDsdRecursive( pNtkRes, fVerbose ) )
            {
                fprintf( pErr, "Recursive decomposition has failed.\n" );
                Abc_NtkDelete( pNtkRes );
                return 1;
            }
        }
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    else if ( fRecursive )
    {
        if ( !Abc_NtkIsLogicBdd( pNtk ) )
        {
            fprintf( pErr, "This command is only applicable to logic BDD networks.\n" );
            return 1;
        }
        if ( !Abc_NtkDsdRecursive( pNtk, fVerbose ) )
            fprintf( pErr, "Recursive decomposition has failed.\n" );
    }
    return 0;

usage:
    fprintf( pErr, "usage: dsd [-grvpsh]\n" );
    fprintf( pErr, "\t     decomposes the network using disjoint-support decomposition\n" );
    fprintf( pErr, "\t-g     : collapses the network and decomposes shared BDDs [default = %s]\n", fGlobal? "yes": "no" );  
    fprintf( pErr, "\t-r     : applied DSD and MUX-decomposition recursively [default = %s]\n", fRecursive? "yes": "no" );  
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
int Abc_CommandRes( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    Abc_ManRes_t * p;
    extern int Abc_NtkAigResynthesize( Abc_Ntk_t * pNtk, Abc_ManRes_t * p );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    p = Abc_NtkManResStart();
    p->fVerbose     =  0;
    p->nNodeSizeMax = 10;
    p->nConeSizeMax = 10;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ncvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-n\" should be followed by an integer.\n" );
                goto usage;
            }
            p->nNodeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( p->nNodeSizeMax < 0 ) 
                goto usage;
            break;
        case 'c':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-c\" should be followed by an integer.\n" );
                goto usage;
            }
            p->nConeSizeMax = atoi(argv[util_optind]);
            util_optind++;
            if ( p->nConeSizeMax < 0 ) 
                goto usage;
            break;
        case 'v':
            p->fVerbose ^= 1;
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
        Abc_NtkManResStop( p );
        return 1;
    }
    if ( !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "This command can only be applied to an AIG.\n" );
        Abc_NtkManResStop( p );
        return 1;
    }
    if ( Abc_NtkCountChoiceNodes(pNtk) )
    {
        fprintf( pErr, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        Abc_NtkManResStop( p );
        return 1;
    }

    // modify the current network
    Abc_NtkAigResynthesize( pNtk, p );
    return 0;

usage:
    fprintf( pErr, "usage: res [-n num] [-c num] [-vh]\n" );
    fprintf( pErr, "\t         performs technology-independent resynthesis of the AIG\n" );
    fprintf( pErr, "\t-n num : the max support of the collapsed node [default = %d]\n", p->nNodeSizeMax );  
    fprintf( pErr, "\t-c num : the max support of the containing cone [default = %d]\n", p->nConeSizeMax );  
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", p->fVerbose? "yes": "no" );
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
    pNtkRes = Abc_NtkLogic( pNtk );
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
    if ( !Abc_NtkPrepareCommand( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
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
    while ( ( c = util_getopt( argc, argv, "fih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-n\" should be followed by an integer.\n" );
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
    if ( !Abc_NtkIsAig(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0 );
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
    fprintf( pErr, "usage: frames [-f num] [-ih]\n" );
    fprintf( pErr, "\t         unrolls the network for a number of time frames\n" );
    fprintf( pErr, "\t-f num : the number of frames to unroll [default = %d]\n", nFrames );
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
    if ( !Abc_NtkIsLogicBdd(pNtk) )
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
    if ( !Abc_NtkIsLogicSop(pNtk) )
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
    if ( !(Abc_NtkIsLogicSop(pNtk) || Abc_NtkIsLogicBdd(pNtk)) )
    {
        fprintf( stdout, "First convert node representation into BDDs or SOPs.\n" );
        return 0;
    }
    if ( Abc_NtkIsLogicSop(pNtk) )
    {
//        printf( "Converting node functions from SOP to BDD.\n" );
        Abc_NtkSopToBdd(pNtk);
    }

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
    if ( !Abc_NtkIsAig(pNtk) )
    {
        fprintf( stdout, "This command works only for AIGs.\n" );
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
int Abc_CommandFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Fraig_Params_t Params;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fAllNodes;
    int c;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fAllNodes = 0;
    Params.nPatsRand  = 2048; // the number of words of random simulation info
    Params.nPatsDyna  = 2048; // the number of words of dynamic simulation info
    Params.nBTLimit   = 99;   // the max number of backtracks to perform
    Params.fFuncRed   =  1;   // performs only one level hashing
    Params.fFeedBack  =  1;   // enables solver feedback
    Params.fDist1Pats =  1;   // enables distance-1 patterns
    Params.fDoSparse  =  0;   // performs equiv tests for sparse functions 
    Params.fChoicing  =  0;   // enables recording structural choices
    Params.fTryProve  =  0;   // tries to solve the final miter
    Params.fVerbose   =  0;   // the verbosiness flag
    Params.fVerboseP  =  0;   // the verbosiness flag
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "RDBrscpvah" ) ) != EOF )
    {
        switch ( c )
        {

        case 'R':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-r\" should be followed by an integer.\n" );
                goto usage;
            }
            Params.nPatsRand = atoi(argv[util_optind]);
            util_optind++;
            if ( Params.nPatsRand < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-d\" should be followed by an integer.\n" );
                goto usage;
            }
            Params.nPatsDyna = atoi(argv[util_optind]);
            util_optind++;
            if ( Params.nPatsDyna < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-b\" should be followed by an integer.\n" );
                goto usage;
            }
            Params.nBTLimit = atoi(argv[util_optind]);
            util_optind++;
            if ( Params.nBTLimit < 0 ) 
                goto usage;
            break;

        case 'r':
            Params.fFuncRed ^= 1;
            break;
        case 's':
            Params.fDoSparse ^= 1;
            break;
        case 'c':
            Params.fChoicing ^= 1;
            break;
        case 'p':
            Params.fTryProve ^= 1;
            break;
        case 'v':
            Params.fVerbose ^= 1;
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
    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Can only fraig a logic network.\n" );
        return 1;
    }

    // report the proof
    Params.fVerboseP = Params.fTryProve;

    // get the new network
    if ( Abc_NtkIsAig(pNtk) )
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0 );
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Fraiging has failed.\n" );
        return 1;
    }

    if ( Params.fTryProve ) // report the result
        Abc_NtkMiterReport( pNtkRes );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    sprintf( Buffer, "%d", Params.nBTLimit );
    fprintf( pErr, "usage: fraig [-R num] [-D num] [-B num] [-rscpvah]\n" );
    fprintf( pErr, "\t         transforms a logic network into a functionally reduced AIG\n" );
    fprintf( pErr, "\t-R num : number of random patterns (127 < num < 32769) [default = %d]\n",     Params.nPatsRand );
    fprintf( pErr, "\t-D num : number of systematic patterns (127 < num < 32769) [default = %d]\n", Params.nPatsDyna );
    fprintf( pErr, "\t-B num : number of backtracks for one SAT problem [default = %s]\n",    Params.nBTLimit==-1? "infinity" : Buffer );
    fprintf( pErr, "\t-r     : toggle functional reduction [default = %s]\n",                 Params.fFuncRed? "yes": "no" );
    fprintf( pErr, "\t-s     : toggle considering sparse functions [default = %s]\n",         Params.fDoSparse? "yes": "no" );
    fprintf( pErr, "\t-c     : toggle accumulation of choices [default = %s]\n",              Params.fChoicing? "yes": "no" );
    fprintf( pErr, "\t-p     : toggle proving the final miter [default = %s]\n",              Params.fTryProve? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n",                       Params.fVerbose?  "yes": "no" );
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
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( pErr, "Cannot sweep a netlist. Please transform into a logic network.\n" );
        return 1;
    }
    if ( Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Cannot sweep AIGs (use \"fraig\").\n" );
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
    int fVerbose;
    int fSweep;
    int c;
    extern Abc_Ntk_t * Abc_NtkMap( Abc_Ntk_t * pNtk, double DelayTarget, int fRecovery, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    DelayTarget =-1;
    fRecovery   = 1;
    fSweep      = 1;
    fVerbose    = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "dasvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-d\" should be followed by a floating point number.\n" );
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

    if ( !Abc_NtkIsAig(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0 );
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
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fVerbose );
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
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fVerbose );
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
    fprintf( pErr, "usage: map [-d num] [-asvh]\n" );
    fprintf( pErr, "\t         performs standard cell mapping of the current network\n" );
    fprintf( pErr, "\t-d num : sets the global required times [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-a     : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    fprintf( pErr, "\t-s     : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
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
    if ( !Abc_NtkIsLogicMap(pNtk) )
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

    if ( !Abc_NtkIsLogicSop(pNtk) )
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

    if ( !Abc_NtkIsAig(pNtk) )
    {
        fprintf( pErr, "Works only for the AIG representation.\n" );
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
    fprintf( pErr, "\t        performs superchoicing\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkFpga( Abc_Ntk_t * pNtk, int fRecovery, int fVerbose );

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fRecovery  = 1;
    fVerbose   = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "avh" ) ) != EOF )
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
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsAig(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0 );
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
        pNtkRes = Abc_NtkFpga( pNtk, fRecovery, fVerbose );
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
        pNtkRes = Abc_NtkFpga( pNtk, fRecovery, fVerbose );
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
    fprintf( pErr, "usage: fpga [-avh]\n" );
    fprintf( pErr, "\t        performs FPGA mapping of the current network\n" );
    fprintf( pErr, "\t-a    : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
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
int Abc_CommandCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;

    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
    extern void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );


    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fSat   = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSat ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + util_optind;
    nArgcNew = argc - util_optind;
    if ( !Abc_NtkPrepareCommand( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // perform equivalence checking
    if ( fSat )
        Abc_NtkCecSat( pNtk1, pNtk2 );
    else
        Abc_NtkCecFraig( pNtk1, pNtk2 );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: cec [-sh] <file1> <file2>\n" );
    fprintf( pErr, "\t        performs combinational equivalence checking\n" );
    fprintf( pErr, "\t-s    : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
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
    while ( ( c = util_getopt( argc, argv, "fsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            if ( util_optind >= argc )
            {
                fprintf( pErr, "Command line switch \"-t\" should be followed by an integer.\n" );
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
    if ( !Abc_NtkPrepareCommand( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
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
    fprintf( pErr, "usage: sec [-sh] [-f num] <file1> <file2>\n" );
    fprintf( pErr, "\t         performs bounded sequential equivalence checking\n" );
    fprintf( pErr, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t-f num : the number of time frames to use [default = %d]\n", nFrames );
    fprintf( pErr, "\tfile1  : (optional) the file with the first network\n");
    fprintf( pErr, "\tfile2  : (optional) the file with the second network\n");
    fprintf( pErr, "\t         if no files are given, uses the current network and its spec\n");
    fprintf( pErr, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


