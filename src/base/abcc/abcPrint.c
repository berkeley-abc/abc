/**CFile****************************************************************

  FileName    [abcPrint.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Statistics and visualization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "proof/fraig/fraig.h"
#include "opt/cut/cut.h"
#include "opt/sim/sim.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandPrintStats             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintExdc              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintIo                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLatch             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFanio             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintMffc              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFactor            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLevel             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSupport           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintNpn               ( Abc_Frame_t * pAbc, int argc, char ** argv );
#ifdef ABC_USE_CUDD
static int Abc_CommandPrintMint              ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
static int Abc_CommandPrintSymms             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintUnate             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintAuto              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintKMap              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintGates             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSharing           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintXCut              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintDsd               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintCone              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintMiter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintStatus            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintDelay             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShow                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowBdd                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowCut                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Ps                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PFan               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Pms                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PSig               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Status             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MuxProfile         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PrintTruth         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Unate              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Show               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Struct             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PrintPath          ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers statistics and visualization commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitPrint( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Printing",     "ps",            Abc_CommandPrintStats,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_stats",   Abc_CommandPrintStats,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_exdc",    Abc_CommandPrintExdc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_io",      Abc_CommandPrintIo,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_latch",   Abc_CommandPrintLatch,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "pfan",          Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_fanio",   Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_mffc",    Abc_CommandPrintMffc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "pf",            Abc_CommandPrintFactor,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_factor",  Abc_CommandPrintFactor,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_level",   Abc_CommandPrintLevel,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "psu",           Abc_CommandPrintSupport,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_supp",    Abc_CommandPrintSupport,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_npn",     Abc_CommandPrintNpn,         0 );
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "Printing",     "print_mint",    Abc_CommandPrintMint,        0 );
#endif
    Cmd_CommandAdd( pAbc, "Printing",     "print_symm",    Abc_CommandPrintSymms,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_unate",   Abc_CommandPrintUnate,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_auto",    Abc_CommandPrintAuto,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_kmap",    Abc_CommandPrintKMap,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "pg",            Abc_CommandPrintGates,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_gates",   Abc_CommandPrintGates,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_sharing", Abc_CommandPrintSharing,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_xcut",    Abc_CommandPrintXCut,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_dsd",     Abc_CommandPrintDsd,         0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_cone",    Abc_CommandPrintCone,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_miter",   Abc_CommandPrintMiter,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_status",  Abc_CommandPrintStatus,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_delay",   Abc_CommandPrintDelay,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show",          Abc_CommandShow,             0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_bdd",      Abc_CommandShowBdd,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_cut",      Abc_CommandShowCut,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&ps",           Abc_CommandAbc9Ps,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&pfan",         Abc_CommandAbc9PFan,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&pms",          Abc_CommandAbc9Pms,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&psig",         Abc_CommandAbc9PSig,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&status",       Abc_CommandAbc9Status,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&profile",      Abc_CommandAbc9MuxProfile,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&print_truth",  Abc_CommandAbc9PrintTruth,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&unate",        Abc_CommandAbc9Unate,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&show",         Abc_CommandAbc9Show,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&struct",       Abc_CommandAbc9Struct,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&print_path",   Abc_CommandAbc9PrintPath,              0 );
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
int Abc_CommandPrintStats( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fFactor;
    int fSaveBest;
    int fDumpResult;
    int fUseLutLib;
    int fPrintTime;
    int fPrintMuxes;
    int fPower;
    int fGlitch;
    int fSkipBuf;
    int fSkipSmall;
    int fPrintMem;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);

    // set the defaults
    fFactor   = 0;
    fSaveBest = 0;
    fDumpResult = 0;
    fUseLutLib = 0;
    fPrintTime = 0;
    fPrintMuxes = 0;
    fPower = 0;
    fGlitch = 0;
    fSkipBuf = 0;
    fSkipSmall = 0;
    fPrintMem = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fbdltmpgscuh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFactor ^= 1;
            break;
        case 'b':
            fSaveBest ^= 1;
            break;
        case 'd':
            fDumpResult ^= 1;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 't':
            fPrintTime ^= 1;
            break;
        case 'm':
            fPrintMuxes ^= 1;
            break;
        case 'p':
            fPower ^= 1;
            break;
        case 'g':
            fGlitch ^= 1;
            break;
        case 's':
            fSkipBuf ^= 1;
            break;
        case 'c':
            fSkipSmall ^= 1;
            break;
        case 'u':
            fPrintMem ^= 1;
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
    if ( !Abc_NtkIsLogic(pNtk) && fUseLutLib )
    {
        Abc_Print( -1, "Cannot print LUT delay for a non-logic network.\n" );
        return 1;
    }
    Abc_NtkPrintStats( pNtk, fFactor, fSaveBest, fDumpResult, fUseLutLib, fPrintMuxes, fPower, fGlitch, fSkipBuf, fSkipSmall, fPrintMem );
    if ( fPrintTime )
    {
        pAbc->TimeTotal += pAbc->TimeCommand;
        Abc_Print( 1, "elapse: %3.2f seconds, total: %3.2f seconds\n", pAbc->TimeCommand, pAbc->TimeTotal );
        pAbc->TimeCommand = 0.0;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_stats [-fbdltmpgscuh]\n" );
    Abc_Print( -2, "\t        prints the network statistics\n" );
    Abc_Print( -2, "\t-f    : toggles printing the literal count in the factored forms [default = %s]\n", fFactor? "yes": "no" );
    Abc_Print( -2, "\t-b    : toggles saving the best logic network in \"best.blif\" [default = %s]\n", fSaveBest? "yes": "no" );
    Abc_Print( -2, "\t-d    : toggles dumping statistics about the network into file [default = %s]\n", fDumpResult? "yes": "no" );
    Abc_Print( -2, "\t-l    : toggles printing delay of LUT mapping using LUT library [default = %s]\n", fUseLutLib? "yes": "no" );
    Abc_Print( -2, "\t-t    : toggles printing runtime statistics [default = %s]\n", fPrintTime? "yes": "no" );
    Abc_Print( -2, "\t-m    : toggles printing MUX statistics [default = %s]\n", fPrintMuxes? "yes": "no" );
    Abc_Print( -2, "\t-p    : toggles printing power dissipation due to switching [default = %s]\n", fPower? "yes": "no" );
    Abc_Print( -2, "\t-g    : toggles printing percentage of increased power due to glitching [default = %s]\n", fGlitch? "yes": "no" );
    Abc_Print( -2, "\t-s    : toggles not counting single-output nodes as nodes [default = %s]\n", fSkipBuf? "yes": "no" );
    Abc_Print( -2, "\t-c    : toggles not counting constants and single-output nodes as nodes [default = %s]\n", fSkipSmall? "yes": "no" );
    Abc_Print( -2, "\t-u    : toggles printing memory usage [default = %s]\n", fPrintMem? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintExdc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    double Percentage;
    int fShort;
    int c;
    int fPrintDc;
    extern double Abc_NtkSpacePercentage( Abc_Obj_t * pNode );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set the defaults
    fShort  = 1;
    fPrintDc = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sdh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShort ^= 1;
            break;
        case 'd':
            fPrintDc ^= 1;
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
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "Network has no EXDC.\n" );
        return 1;
    }

    if ( fPrintDc )
    {
        if ( !Abc_NtkIsStrash(pNtk->pExdc) )
        {
            pNtkTemp = Abc_NtkStrash(pNtk->pExdc, 0, 0, 0);
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtkTemp, 0) ) );
            Abc_NtkDelete( pNtkTemp );
        }
        else
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtk->pExdc, 0) ) );

        Abc_Print( 1, "EXDC network statistics: " );
        Abc_Print( 1, "(" );
        if ( Percentage > 0.05 && Percentage < 99.95 )
            Abc_Print( 1, "%.2f", Percentage );
        else if ( Percentage > 0.000005 && Percentage < 99.999995 )
            Abc_Print( 1, "%.6f", Percentage );
        else
            Abc_Print( 1, "%f", Percentage );
        Abc_Print( 1, " %% don't-cares)\n" );
    }
    else
        Abc_Print( 1, "EXDC network statistics: \n" );
    Abc_NtkPrintStats( pNtk->pExdc, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: print_exdc [-dh]\n" );
    Abc_Print( -2, "\t        prints the EXDC network statistics\n" );
    Abc_Print( -2, "\t-d    : toggles printing don't-care percentage [default = %s]\n", fPrintDc? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c, fPrintFlops = 1;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fPrintFlops ^= 1;
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

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintFanio( stdout, pNode );
        return 0;
    }
    // print the nodes
    Abc_NtkPrintIo( stdout, pNtk, fPrintFlops );
    return 0;

usage:
    Abc_Print( -2, "usage: print_io [-fh] <node>\n" );
    Abc_Print( -2, "\t        prints the PIs/POs/flops or fanins/fanouts of a node\n" );
    Abc_Print( -2, "\t-f    : toggles printing flops [default = %s]\n", fPrintFlops? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : the node to print fanins/fanouts\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fPrintSccs;
    extern void Abc_NtkPrintSccs( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fPrintSccs = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fPrintSccs ^= 1;
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
    // print the nodes
    Abc_NtkPrintLatch( stdout, pNtk );
    if ( fPrintSccs )
        Abc_NtkPrintSccs( pNtk, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: print_latch [-sh]\n" );
    Abc_Print( -2, "\t        prints information about latches\n" );
    Abc_Print( -2, "\t-s    : toggles printing SCCs of registers [default = %s]\n", fPrintSccs? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseFanio = 0;
    int fUsePio   = 0;
    int fUseSupp  = 0;
    int fUseCone  = 0;
    int fMffc     = 0;
    int fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fiscmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fUseFanio ^= 1;
            break;
        case 'i':
            fUsePio ^= 1;
            break;
        case 's':
            fUseSupp ^= 1;
            break;
        case 'c':
            fUseCone ^= 1;
            break;
        case 'm':
            fMffc ^= 1;
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
    // print the nodes
    if ( fMffc || !fVerbose )
        Abc_NtkPrintFanioNew( stdout, pNtk, fMffc );
    else
    {
        if ( fUseFanio + fUsePio + fUseSupp + fUseCone == 1 )
            Abc_NtkPrintFanio( stdout, pNtk, fUseFanio, fUsePio, fUseSupp, fUseCone );
        else
            printf( "Exactly one of the switches \"-f\", \"-i\", \"-s\", \"-c\" should be enabled.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_fanio [-fiscmvh]\n" );
    Abc_Print( -2, "\t        prints the statistics about different objects in the network\n" );
    Abc_Print( -2, "\t-f    : toggles considering fanins/fanouts of all nodes [default = %s]\n", fUseFanio? "yes": "no" );
    Abc_Print( -2, "\t-i    : toggles considering fanins/fanouts of CI/CO [default = %s]\n", fUsePio? "yes": "no" );
    Abc_Print( -2, "\t-s    : toggles considering TFO/TFI support sizes of CI/CO [default = %s]\n", fUseSupp? "yes": "no" );
    Abc_Print( -2, "\t-c    : toggles considering TFO/TFI cone sizes of CI/CO [default = %s]\n", fUseCone? "yes": "no" );
    Abc_Print( -2, "\t-m    : toggles printing MFFC sizes instead of fanouts [default = %s]\n", fMffc? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggles verbose way of printing the stats [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintMffc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern void Abc_NtkPrintMffc( FILE * pFile, Abc_Ntk_t * pNtk );

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

    // print the nodes
    Abc_NtkPrintMffc( stdout, pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_mffc [-h]\n" );
    Abc_Print( -2, "\t        prints the MFFC of each node in the network\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    extern void Abc_NodePrintSop( FILE * pFile, Abc_Obj_t * pNode, int fUseRealNames );
    extern void Abc_NtkPrintSop( FILE * pFile, Abc_Ntk_t * pNtk, int fUseRealNames );

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c, fSop = 0;
    int fUseRealNames;

    // set defaults
    fUseRealNames = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "snh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSop ^= 1;
            break;
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Printing factored forms can be done for SOP networks.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        if ( fSop )
            Abc_NodePrintSop( stdout, pNode, fUseRealNames );
        else
            Abc_NodePrintFactor( stdout, pNode, fUseRealNames );
        return 0;
    }
    // print the nodes
    if ( fSop )
        Abc_NtkPrintSop( stdout, pNtk, fUseRealNames );
    else
        Abc_NtkPrintFactor( stdout, pNtk, fUseRealNames );
    return 0;

usage:
    Abc_Print( -2, "usage: print_factor [-snh] <node>\n" );
    Abc_Print( -2, "\t        prints the factored forms (FFs) of nodes\n" );
    Abc_Print( -2, "\t-s    : toggles printing SOP instead of FF [default = %s]\n", fSop? "SOP": "FF" );
    Abc_Print( -2, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : (optional) one node to consider\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int fListNodes;
    int fProfile;
    int fOutputs;
    int fVerbose;

    // set defaults
    fListNodes = 0;
    fProfile   = 1;
    fOutputs   = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "npovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fListNodes ^= 1;
            break;
        case 'p':
            fProfile ^= 1;
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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !fProfile && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintLevel( stdout, pNode );
        return 0;
    }
    // process all COs
    Abc_NtkPrintLevel( stdout, pNtk, fProfile, fListNodes, fOutputs, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_level [-npovh] <node>\n" );
    Abc_Print( -2, "\t        prints information about node level and cone size\n" );
    Abc_Print( -2, "\t-n    : toggles printing nodes by levels [default = %s]\n", fListNodes? "yes": "no" );
    Abc_Print( -2, "\t-p    : toggles printing level profile [default = %s]\n", fProfile? "yes": "no" );
    Abc_Print( -2, "\t-o    : toggles printing output levels [default = %s]\n", fOutputs? "yes": "no" );
    Abc_Print( -2, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : (optional) one node to consider\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fStruct;
    int fVerbose;
    int fVeryVerbose;
    extern Vec_Ptr_t * Sim_ComputeFunSupp( Abc_Ntk_t * pNtk, int fVerbose );
    extern void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk, int fMatrix );

    // set defaults
    fStruct = 1;
    fVerbose = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fStruct ^= 1;
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

    // print support information
    if ( fStruct )
    {
        Abc_NtkPrintStrSupports( pNtk, fVeryVerbose );
        return 0;
    }

    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational networks (run \"comb\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    vSuppFun = Sim_ComputeFunSupp( pNtk, fVerbose );
    ABC_FREE( vSuppFun->pArray[0] );
    Vec_PtrFree( vSuppFun );
    return 0;

usage:
    Abc_Print( -2, "usage: print_supp [-svwh]\n" );
    Abc_Print( -2, "\t        prints the supports of the CO nodes\n" );
    Abc_Print( -2, "\t-s    : toggle printing structural support only [default = %s].\n", fStruct? "yes": "no" );
    Abc_Print( -2, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w    : enable printing CI/CO dependency matrix [default = %s].\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintNpn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Dau_PrintNpnFunctions( word * p, int nVars, int fVerbose );
    char * pTruthStr = NULL;
    word   pTruth[16] = {0};
    int c, nVars, fVerbose = 0;
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
    if ( globalUtilOptind != argc-1 )
    {
        Abc_Print( -1, "The command expects the truth table on the command line.\n" );
        goto usage;
    }
    pTruthStr = argv[globalUtilOptind];
    nVars = Abc_TtReadHex( pTruth, pTruthStr );
    assert( nVars <= 10 );
    Dau_PrintNpnFunctions( pTruth, nVars, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_npn [-vh] <truth>\n" );
    Abc_Print( -2, "\t           prints the NPN members of the given function\n" );
    Abc_Print( -2, "\t-v       : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t<truth>  : the truth table in hexadecimal notation\n");
    
    return 1;
}

#ifdef ABC_USE_CUDD
/**Function*************************************************************

  Synopsis    [Prints the minterms of the current network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintMint( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pObj;
    int c;
    int fVerbose;

    // set defaults
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svwh" ) ) != EOF )
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
        Abc_Print( -1, "This command works only for logic networks (run \"clp\").\n" );
        return 1;
    }
    if ( !Abc_NtkHasBdd(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks with local functions represented by BDDs.\n" );
        return 1;
    }

    Abc_NtkForEachNode( pNtk, pObj, c )
        printf( "ObjId %3d : SuppSize = %5d   MintCount = %32.0f\n", c, Abc_ObjFaninNum(pObj), 
            Cudd_CountMinterm((DdManager *)pNtk->pManFunc, (DdNode *)pObj->pData, Abc_ObjFaninNum(pObj)) );
    return 0;

usage:
    Abc_Print( -2, "usage: print_mint [-svwh]\n" );
    Abc_Print( -2, "\t        prints the number of on-set minterms in the PO functions\n" );
    Abc_Print( -2, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}
#endif

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSymms( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseBdds;
    int fNaive;
    int fReorder;
    int fVerbose;
    extern void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fReorder, int fVerbose );

    // set defaults
    fUseBdds = 0;
    fNaive   = 0;
    fReorder = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bnrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fUseBdds ^= 1;
            break;
        case 'n':
            fNaive ^= 1;
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
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational networks (run \"comb\").\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_symm [-bnrvh]\n" );
    Abc_Print( -2, "\t         computes symmetries of the PO functions\n" );
    Abc_Print( -2, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );
    Abc_Print( -2, "\t-n     : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s].\n", fReorder? "yes": "no" );
    Abc_Print( -2, "\t-v     : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseBdds;
    int fUseNaive;
    int fVerbose;
    extern void Abc_NtkPrintUnate( Abc_Ntk_t * pNtk, int fUseBdds, int fUseNaive, int fVerbose );

    // set defaults
    fUseBdds  = 1;
    fUseNaive = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fUseBdds ^= 1;
            break;
        case 'n':
            fUseNaive ^= 1;
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
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    Abc_NtkPrintUnate( pNtk, fUseBdds, fUseNaive, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_unate [-bnvh]\n" );
    Abc_Print( -2, "\t         computes unate variables of the PO functions\n" );
    Abc_Print( -2, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );
    Abc_Print( -2, "\t-n     : toggle naive BDD-based computation [default = %s].\n", fUseNaive? "yes": "no" );
    Abc_Print( -2, "\t-v     : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintAuto( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int Output;
    int fNaive;
    int fVerbose;
    extern void Abc_NtkAutoPrint( Abc_Ntk_t * pNtk, int Output, int fNaive, int fVerbose );

    // set defaults
    Output   = -1;
    fNaive   = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Onvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            Output = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Output < 0 )
                goto usage;
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }


    Abc_NtkAutoPrint( pNtk, Output, fNaive, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_auto [-O <num>] [-nvh]\n" );
    Abc_Print( -2, "\t           computes autosymmetries of the PO functions\n" );
    Abc_Print( -2, "\t-O <num> : (optional) the 0-based number of the output [default = all]\n");
    Abc_Print( -2, "\t-n       : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );
    Abc_Print( -2, "\t-v       : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintKMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int fUseRealNames;

    extern void Abc_NodePrintKMap( Abc_Obj_t * pNode, int fUseRealNames );

    // set defaults
    fUseRealNames = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nh" ) ) != EOF )
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
    if ( argc == globalUtilOptind + 2 )
    {
        Abc_NtkShow6VarFunc( argv[globalUtilOptind], argv[globalUtilOptind+1] );
        return 0;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Visualization of Karnaugh maps works for logic networks.\n" );
        return 1;
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            Abc_Print( -1, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    Abc_NtkToBdd(pNtk);
    Abc_NodePrintKMap( pNode, fUseRealNames );
    return 0;

usage:
    Abc_Print( -2, "usage: print_kmap [-nh] <node>\n" );
    Abc_Print( -2, "\t        shows the truth table of the node\n" );
    Abc_Print( -2, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\t<node>: the node to consider (default = the driver of the first PO)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintGates( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;
    int fUpdateProfile;
    int fVerbose;

    extern void Abc_NtkPrintGates( Abc_Ntk_t * pNtk, int fUseLibrary, int fUpdateProfile );
    extern void Abc_NtkPrintGates2( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    fUpdateProfile = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "luvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'u':
            fUpdateProfile ^= 1;
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
        Abc_Print( -1, "Printing gates does not work for AIGs and sequential AIGs.\n" );
        return 1;
    }
    if ( fVerbose )
        Abc_NtkPrintGates2( pNtk );
    else
        Abc_NtkPrintGates( pNtk, fUseLibrary, fUpdateProfile );
    return 0;

usage:
    Abc_Print( -2, "usage: print_gates [-luvh]\n" );
    Abc_Print( -2, "\t        prints statistics about gates used in the network\n" );
    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-u    : update profile before printing it[default = %s]\n", fUpdateProfile? "yes": "no" );
    Abc_Print( -2, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSharing( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintSharing( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
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
    Abc_NtkPrintSharing( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_sharing [-h]\n" );
    Abc_Print( -2, "\t        prints the number of shared nodes in the TFI cones of the COs\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintXCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern int Abc_NtkCrossCut( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
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
    Abc_NtkCrossCut( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_xcut [-h]\n" );
    Abc_Print( -2, "\t        prints the size of the cross cut of the current network\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintDsd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fCofactor;
    int nCofLevel;
    int fProfile;
    int fPrintDec;

    extern void Kit_DsdTest( unsigned * pTruth, int nVars );
    extern void Kit_DsdPrintCofactors( unsigned * pTruth, int nVars, int nCofLevel, int fVerbose );
    extern void Dau_DecTrySets( word * p, int nVars, int fVerbose );

    // set defaults
    nCofLevel = 1;
    fCofactor = 0;
    fProfile  = 0;
    fPrintDec = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Npcdh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nCofLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCofLevel < 0 )
                goto usage;
            break;
        case 'p':
            fProfile ^= 1;
            break;
        case 'c':
            fCofactor ^= 1;
            break;
        case 'd':
            fPrintDec ^= 1;
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
    // get the truth table of the first output
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Currently works only for logic networks.\n" );
        return 1;
    }
    Abc_NtkToAig( pNtk );
    // convert it to truth table
    {
        Abc_Obj_t * pObj = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        Vec_Int_t * vMemory;
        unsigned * pTruth;
        if ( !Abc_ObjIsNode(pObj) )
        {
            Abc_Print( -1, "The fanin of the first PO node does not have a logic function.\n" );
            return 1;
        }
        if ( Abc_ObjFaninNum(pObj) > 16 )
        {
            Abc_Print( -1, "Currently works only for up to 16 inputs.\n" );
            return 1;
        }
        vMemory = Vec_IntAlloc(0);
        pTruth = Hop_ManConvertAigToTruth( (Hop_Man_t *)pNtk->pManFunc, Hop_Regular((Hop_Obj_t *)pObj->pData), Abc_ObjFaninNum(pObj), vMemory, 0 );
        if ( Hop_IsComplement((Hop_Obj_t *)pObj->pData) )
            Extra_TruthNot( pTruth, pTruth, Abc_ObjFaninNum(pObj) );
//        Extra_PrintBinary( stdout, pTruth, 1 << Abc_ObjFaninNum(pObj) );
//        Abc_Print( -1, "\n" );
        if ( fPrintDec )//&&Abc_ObjFaninNum(pObj) <= 6 )
        {
            word * pTruthW = (word *)pTruth;
            if ( Abc_ObjFaninNum(pObj) < 6 )
                pTruthW[0] = Abc_Tt6Stretch( pTruthW[0], Abc_ObjFaninNum(pObj) );
            Dau_DecTrySets( (word *)pTruth, Abc_ObjFaninNum(pObj), 1 );
        }
        if ( fProfile )
            Kit_TruthPrintProfile( pTruth, Abc_ObjFaninNum(pObj) );
        else if ( fCofactor )
            Kit_DsdPrintCofactors( pTruth, Abc_ObjFaninNum(pObj), nCofLevel, 1 );
        else
            Kit_DsdTest( pTruth, Abc_ObjFaninNum(pObj) );
        Vec_IntFree( vMemory );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_dsd [-pcdh] [-N <num>]\n" );
    Abc_Print( -2, "\t           print DSD formula for a single-output function with less than 16 variables\n" );
    Abc_Print( -2, "\t-p       : toggle printing profile [default = %s]\n", fProfile? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle recursive cofactoring [default = %s]\n", fCofactor? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggle printing decompositions [default = %s]\n", fPrintDec? "yes": "no" );
    Abc_Print( -2, "\t-N <num> : the number of levels to cofactor [default = %d]\n", nCofLevel );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintCone( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
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
        Abc_Print( -1, "The network is combinational.\n" );
        return 1;
    }
    Abc_NtkDarPrintCone( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_cone [-h]\n" );
    Abc_Print( -2, "\t        prints cones of influence info for each primary output\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintMiter( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
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
        Abc_Print( -1, "The network is should be structurally hashed.\n" );
        return 1;
    }
    Abc_NtkPrintMiter( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_miter [-h]\n" );
    Abc_Print( -2, "\t        prints the status of the miter\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintStatus( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkDumpOneCexSpecial( FILE * pFile, Abc_Ntk_t * pNtk, Abc_Cex_t * pCex );
    extern void Abc_NtkPrintPoEquivs( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fOutStatus = 0, fShort = 1;
    char * pLogFileName = NULL;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Losh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'o':
            fOutStatus ^= 1;
            break;
        case 's':
            fShort ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fOutStatus )
    {
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Empty network.\n" );
            return 1;
        }
        Abc_NtkPrintPoEquivs( pNtk );
        return 0;
    }
    if ( !pAbc->vStatuses )
        Abc_Print( 1,"Status = %d  Frames = %d   ", pAbc->Status, pAbc->nFrames );
    if ( pAbc->pCex == NULL && pAbc->vCexVec == NULL )
        Abc_Print( 1,"Cex is not defined.\n" );
    else
    {
        if ( pAbc->pCex )
            Abc_CexPrintStats( pAbc->pCex );
        if ( pAbc->vCexVec )
        {
            Abc_Cex_t * pTemp;
            int nCexes = 0;
            int Counter = 0;
            //printf( "\n" );
            Vec_PtrForEachEntry( Abc_Cex_t *, pAbc->vCexVec, pTemp, c )
            {
                if ( pTemp == (void *)(ABC_PTRINT_T)1 )
                {
                    Counter++;
                    continue;
                }
                if ( pTemp )
                {
                    printf( "%4d : ", ++nCexes );
                    Abc_CexPrintStats( pTemp );
                }
            }
//            if ( Counter )
//                printf( "In total, %d (out of %d) outputs are \"sat\" but CEXes are not recorded.\n", Counter, Vec_PtrSize(pAbc->vCexVec) );
        }
    }
    if ( pAbc->vStatuses )
    {
        if ( pLogFileName )
        {
            Abc_Cex_t * pTemp = NULL;
            FILE * pFile = fopen( pLogFileName, "wb" );
            if ( pFile == NULL )
            {
                printf( "Cannot open file \"%s\" for writing.\n", pLogFileName );
                return 0;
            }
            Vec_PtrForEachEntry( Abc_Cex_t *, pAbc->vCexVec, pTemp, c )
            {
                int Status = Vec_IntEntry( pAbc->vStatuses, c );
                if ( Status == -1 ) // undec
                    fprintf( pFile, "STATUS: ABORTED " );
                else if ( Status == 0 )
                    fprintf( pFile, "STATUS: SAT " );
                else if ( Status == 1 )
                    fprintf( pFile, "STATUS: UNSAT " );
                fprintf( pFile, "%s\n", Abc_ObjName(Abc_NtkPo(pNtk, c)) );
                if ( Status != 0 )
                    continue;
                Abc_NtkDumpOneCexSpecial( pFile, pNtk, pTemp );
            }
            fclose( pFile );
        }
        else if ( fShort )
        {
            printf( "Status array contains %d SAT, %d UNSAT, and %d UNDEC entries (out of %d).",
                Vec_IntCountEntry(pAbc->vStatuses, 0), Vec_IntCountEntry(pAbc->vStatuses, 1),
                Vec_IntCountEntry(pAbc->vStatuses, -1), Vec_IntSize(pAbc->vStatuses) );
        }
        else
        {
            int i, Entry;
            Vec_IntForEachEntry( pAbc->vStatuses, Entry, i )
                printf( "%d=%d  ", i, Entry );
        }
        printf( "\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_status [-L file] [-osh]\n" );
    Abc_Print( -2, "\t          prints verification status\n" );
    Abc_Print( -2, "\t-L file : the log file name [default = %s]\n",  pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-o      : toggle printing output status [default = %s]\n", fOutStatus? "yes": "no" );
    Abc_Print( -2, "\t-s      : toggle using short print-out [default = %s]\n", fShort? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintDelay( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pObjIn = NULL, * pObjOut = NULL;
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
    if ( !Abc_NtkIsMappedLogic(pNtk) )
    {
        Abc_Print( -1, "Delay trace works only for network mapped into standard cells.\n" );
        return 1;
    }
    if ( argc > globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    // collect the first name (PO name)
    if ( argc >= globalUtilOptind + 1 )
    {
        int Num = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind], ABC_OBJ_PO );
        if ( Num < 0 )
            Num = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind], ABC_OBJ_BI );
        if ( Num >= 0 )
            pObjOut = Abc_NtkObj( pNtk, Num );
        if ( pObjOut == NULL )
        {
            Abc_Print( 1, "Cannot find combinational output \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    // collect the second name (PI name)
    if ( argc == globalUtilOptind + 2 )
    {
        int Num = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind+1], ABC_OBJ_PI );
        if ( Num < 0 )
            Num = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind+1], ABC_OBJ_BO );
        if ( Num >= 0 )
            pObjIn = Abc_NtkObj( pNtk, Num );
        if ( pObjIn == NULL )
        {
            Abc_Print( 1, "Cannot find combinational input \"%s\".\n", argv[globalUtilOptind+1] );
            return 1;
        }
    }
    Abc_NtkDelayTrace( pNtk, pObjOut, pObjIn, 1 );
    return 0;

usage:
    Abc_Print( -2, "usage: print_delay [-h] <CO_name> <CI_name>\n" );
    Abc_Print( -2, "\t            prints one critical path of the mapped network\n" );
    Abc_Print( -2, "\t-h        : print the command usage\n");
    Abc_Print( -2, "\t<CO_name> : (optional) the sink of the critical path (primary output or flop input)\n");
    Abc_Print( -2, "\t<CI_name> : (optional) the source of the critical path (primary input or flop output)\n");
    Abc_Print( -2, "\t            (if CO and/or CI are not given, uses the most critical ones)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShow( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fSeq;
    int fGateNames;
    int fUseReverse;
    int fFlopDep;
    int fKeepDot;
    int fAigIds;
    extern void Abc_NtkShow( Abc_Ntk_t * pNtk, int fGateNames, int fSeq, int fUseReverse, int fKeepDot, int fAigIds );
    extern void Abc_NtkShowFlopDependency( Abc_Ntk_t * pNtk );

    // set defaults
    fSeq        = 0;
    fGateNames  = 0;
    fUseReverse = 1;
    fFlopDep    = 0;
    fKeepDot    = 0;
    fAigIds     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rsgfdih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fUseReverse ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'g':
            fGateNames ^= 1;
            break;
        case 'f':
            fFlopDep ^= 1;
            break;
        case 'd':
            fKeepDot ^= 1;
            break;
        case 'i':
            fAigIds ^= 1;
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

    if ( fFlopDep )
        Abc_NtkShowFlopDependency( pNtk );
    else
        Abc_NtkShow( pNtk, fGateNames, fSeq, fUseReverse, fKeepDot, fAigIds );
    return 0;

usage:
    Abc_Print( -2, "usage: show [-srgfdih]\n" );
    Abc_Print( -2, "       visualizes the network structure using DOT and GSVIEW\n" );
#ifdef WIN32
    Abc_Print( -2, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t-s    : toggles visualization of sequential networks [default = %s].\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-r    : toggles ordering nodes in reverse order [default = %s].\n", fUseReverse? "yes": "no" );
    Abc_Print( -2, "\t-g    : toggles printing gate names for mapped network [default = %s].\n", fGateNames? "yes": "no" );
    Abc_Print( -2, "\t-f    : toggles visualizing flop dependency graph [default = %s].\n", fFlopDep? "yes": "no" );
    Abc_Print( -2, "\t-d    : toggles keeping the .dot file used to produce the .ps file [default = %s].\n", fKeepDot? "yes": "no" );
    Abc_Print( -2, "\t-i    : toggles using original AIG object IDs as node labels [default = %s].\n", fAigIds? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc); Abc_Obj_t * pNode;
    int c, fCompl = 0, fGlobal = 0, fReorder = 1, fWidth = 0;
    extern void Abc_NodeShowBdd( Abc_Obj_t * pNode, int fCompl );
    extern void Abc_NtkShowBdd( Abc_Ntk_t * pNtk, int fCompl, int fReorder );
    extern void Abc_NtkBddDecExplore( Abc_Obj_t * pNode );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cgrwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fCompl ^= 1;
            break;
        case 'g':
            fGlobal ^= 1;
            break;
        case 'r':
            fReorder ^= 1;
            break;
        case 'w':
            fWidth ^= 1;
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
        Abc_Ntk_t * pTemp = Abc_NtkIsStrash(pNtk) ? pNtk : Abc_NtkStrash(pNtk, 0, 0, 0);
        Abc_NtkShowBdd( pTemp, fCompl, fReorder );
        if ( pTemp != pNtk )
            Abc_NtkDelete( pTemp );
        return 0;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "Visualizing BDDs can only be done for logic BDD networks (run \"bdd\").\n" );
        return 1;
    }    
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            Abc_Print( -1, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    if ( fWidth )
        Abc_NtkBddDecExplore( pNode );
    else
        Abc_NodeShowBdd( pNode, fCompl );
    return 0;

usage:
    Abc_Print( -2, "usage: show_bdd [-cgrwh] <node>\n" );
    Abc_Print( -2, "       uses DOT and GSVIEW to visualize the global BDDs of primary outputs\n" );
    Abc_Print( -2, "       in terms of primary inputs or the local BDD of a node in terms of its fanins\n" );
#ifdef WIN32
    Abc_Print( -2, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t<node>: (optional) the node to consider [default = the driver of the first PO]\n");
    Abc_Print( -2, "\t-c    : toggle visualizing BDD with complemented edges [default = %s].\n", fCompl? "yes": "no" );
    Abc_Print( -2, "\t-g    : toggle visualizing the global BDDs of primary outputs [default = %s].\n", fGlobal? "yes": "no" );
    Abc_Print( -2, "\t-r    : toggles dynamic variable reordering [default = %s]\n", fReorder? "yes": "no" );
    Abc_Print( -2, "\t-w    : toggles printing width profile of the node's BDD [default = %s]\n", fWidth? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int nNodeSizeMax;
    int nConeSizeMax;
    extern void Abc_NodeShowCut( Abc_Obj_t * pNode, int nNodeSizeMax, int nConeSizeMax );

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = ABC_INFINITY;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCh" ) ) != EOF )
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
        Abc_Print( -1, "Visualizing cuts only works for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
        return 1;
    }
    Abc_NodeShowCut( pNode, nNodeSizeMax, nConeSizeMax );
    return 0;

usage:
    Abc_Print( -2, "usage: show_cut [-N <num>] [-C <num>] [-h] <node>\n" );
    Abc_Print( -2, "             visualizes the cut of a node using DOT and GSVIEW\n" );
#ifdef WIN32
    Abc_Print( -2, "             \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "             (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t-N <num> : the max size of the cut to be computed [default = %d]\n", nNodeSizeMax );
    Abc_Print( -2, "\t-C <num> : the max support of the containing cone [default = %d]\n", nConeSizeMax );
    Abc_Print( -2, "\t<node>   : the node to consider\n");
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Ps( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gps_Par_t Pars, * pPars = &Pars;
    int c, fBest = 0;
    memset( pPars, 0, sizeof(Gps_Par_t) );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dtpcnlmasozxbh" ) ) != EOF )
    {
        switch ( c )
        {
        case 't':
            pPars->fTents ^= 1;
            break;
        case 'p':
            pPars->fSwitch ^= 1;
            break;
        case 'c':
            pPars->fCut ^= 1;
            break;
        case 'n':
            pPars->fNpn ^= 1;
            break;
        case 'l':
            pPars->fLutProf ^= 1;
            break;
        case 'm':
            pPars->fMuxXor ^= 1;
            break;
        case 'a':
            pPars->fMiter ^= 1;
            break;
        case 's':
            pPars->fSlacks ^= 1;
            break;
        case 'o':
            pPars->fMapOutStats ^= 1;
            break;
        case 'z':
            pPars->fSkipMap ^= 1;
            break;
        case 'x':
            pPars->fNoColor ^= 1;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pDumpFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'b':
            fBest ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fBest )
    {
        if ( pAbc->pGiaBest == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Ps(): There is no AIG.\n" );
            return 0;
        }
        Gia_ManPrintStats( pAbc->pGiaBest, pPars );
    }
    else
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Ps(): There is no AIG.\n" );
            return 0;
        }
        Gia_ManPrintStats( pAbc->pGia, pPars );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &ps [-tpcnlmasozxbh] [-D file]\n" );
    Abc_Print( -2, "\t          prints stats of the current AIG\n" );
    Abc_Print( -2, "\t-t      : toggle printing BMC tents [default = %s]\n",                pPars->fTents? "yes": "no" );
    Abc_Print( -2, "\t-p      : toggle printing switching activity [default = %s]\n",       pPars->fSwitch? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggle printing the size of frontier cut [default = %s]\n", pPars->fCut? "yes": "no" );
    Abc_Print( -2, "\t-n      : toggle printing NPN classes of functions [default = %s]\n", pPars->fNpn? "yes": "no" );
    Abc_Print( -2, "\t-l      : toggle printing LUT size profile [default = %s]\n",         pPars->fLutProf? "yes": "no" );
    Abc_Print( -2, "\t-m      : toggle printing MUX/XOR statistics [default = %s]\n",       pPars->fMuxXor? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggle printing miter statistics [default = %s]\n",         pPars->fMiter? "yes": "no" );
    Abc_Print( -2, "\t-s      : toggle printing slack distribution [default = %s]\n",       pPars->fSlacks? "yes": "no" );
    Abc_Print( -2, "\t-o      : toggle printing mapping output stats [default = %s]\n",     pPars->fMapOutStats? "yes": "no" );
    Abc_Print( -2, "\t-z      : skip mapping statistics even if mapped [default = %s]\n",   pPars->fSkipMap? "yes": "no" );
    Abc_Print( -2, "\t-x      : toggle using no color in the printout [default = %s]\n",    pPars->fNoColor? "yes": "no" );
    Abc_Print( -2, "\t-b      : toggle printing saved AIG statistics [default = %s]\n",     fBest? "yes": "no" );
    Abc_Print( -2, "\t-D file : file name to dump statistics [default = none]\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PFan( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int nNodes = 0;
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
            nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodes < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9PFan(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManPrintFanio( pAbc->pGia, nNodes );
    return 0;

usage:
    Abc_Print( -2, "usage: &pfan [-N num] [-h]\n" );
    Abc_Print( -2, "\t         prints fanin/fanout statistics\n" );
    Abc_Print( -2, "\t-N num : the number of high-fanout nodes to explore [default = %d]\n", nNodes );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Pms( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Obj_t * pObj;
    int c, nSat = 0;
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PFan(): There is no AIG.\n" );
        return 1;
    }
    printf( "Status of %d outputs of the miter: ", Gia_ManPoNum(pAbc->pGia) );
    Gia_ManForEachPo( pAbc->pGia, pObj, c )
    {
        printf( "%d", c );
        if ( pAbc->pGia->vNamesOut )
           printf( "(%s)", (char *)Vec_PtrEntry(pAbc->pGia->vNamesOut, c) );
        printf( "=%s ", Gia_ObjFaninLit0p(pAbc->pGia, pObj) == 0 ? "unsat":"sat" );
        nSat += Gia_ObjFaninLit0p(pAbc->pGia, pObj) != 0;
    }
    printf( "\n" );
    printf( "Total sat = %d. Total unsat = %d.\n", nSat, Gia_ManPoNum(pAbc->pGia)-nSat );
    return 0;

usage:
    Abc_Print( -2, "usage: &pms [-h]\n" );
    Abc_Print( -2, "\t         prints miter status after SAT sweeping\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PSig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int fSetReset = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fSetReset ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PSigs(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9PSigs(): Works only for sequential circuits.\n" );
        return 1;
    }
    Gia_ManDetectSeqSignals( pAbc->pGia, fSetReset, 1 );
    return 0;

usage:
    Abc_Print( -2, "usage: &psig [-rh]\n" );
    Abc_Print( -2, "\t         prints enable/set/reset statistics\n" );
    Abc_Print( -2, "\t-r     : toggle printing set/reset signals [default = %s]\n", fSetReset? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Status( Abc_Frame_t * pAbc, int argc, char ** argv )
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Status(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManPrintMiterStatus( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &status [-h]\n" );
    Abc_Print( -2, "\t         prints status of the miter\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MuxProfile( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManMuxProfiling( Gia_Man_t * p );
    extern void Gia_ManProfileStructures( Gia_Man_t * p, int nLimit, int fVerbose );
    extern void Acec_StatsCollect( Gia_Man_t * p, int fVerbose );
    extern void Acec_ManProfile( Gia_Man_t * p, int fVerbose );
    int c, fNpn = 0, fMuxes = 0, fAdders = 0, nLimit = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nnmavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimit < 0 )
                goto usage;
            break;
        case 'n':
            fNpn ^= 1;
            break;
        case 'm':
            fMuxes ^= 1;
            break;
        case 'a':
            fAdders ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9MuxProfile(): There is no AIG.\n" );
        return 1;
    }
    if ( fNpn )
    {
        if ( !Gia_ManHasMapping(pAbc->pGia) || Gia_ManLutSizeMax(pAbc->pGia) >= 4 )
        {
            Abc_Print( -1, "Abc_CommandAbc9MuxProfile(): Expecting AIG mapped into 3-LUTs.\n" );
            return 1;
        }
        Acec_StatsCollect( pAbc->pGia, fVerbose );
    }
    else if ( fMuxes )
        Gia_ManMuxProfiling( pAbc->pGia );
    else if ( fAdders )
        Acec_ManProfile( pAbc->pGia, fVerbose );
    else
        Gia_ManProfileStructures( pAbc->pGia, nLimit, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &profile [-N num] [-nmavh]\n" );
    Abc_Print( -2, "\t         profile gate structures appearing in the AIG\n" );
    Abc_Print( -2, "\t-N num : limit on class size to show [default = %d]\n", nLimit );
    Abc_Print( -2, "\t-n     : toggle profiling NPN-classes (for 3-LUT mapped AIGs) [default = %s]\n", fNpn? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle profiling MUX structures [default = %s]\n", fMuxes? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle profiling adder structures [default = %s]\n", fAdders? "yes": "no" );
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
int Abc_CommandAbc9PrintTruth( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern word Gia_LutComputeTruth6Simple( Gia_Man_t * p, int iPo );
    int i, c, iOutNum = 0, nOutRange = -1, fVerbose = 0; word Truth;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ORvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutNum < 0 )
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nOutRange = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOutRange < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9PrintTruth(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPiNum(pAbc->pGia) > 6 )
    {
        Abc_Print( -1, "The number of inputs of the AIG exceeds 6.\n" );
        return 1;
    }
    if ( iOutNum < 0 || iOutNum + nOutRange > Gia_ManPoNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9PrintTruth(): Range of outputs to extract is incorrect.\n" );
        return 1;
    }
    if ( nOutRange == -1 )
        nOutRange = Gia_ManCoNum(pAbc->pGia);
    for ( i = iOutNum; i < iOutNum + nOutRange; i++ )
    {
        Truth = Gia_LutComputeTruth6Simple( pAbc->pGia, i );
        printf( "Output %8d : ", i );
        Extra_PrintHex( stdout, (unsigned *)&Truth, Gia_ManCiNum(pAbc->pGia) );
        printf( "\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &print_truth [-OR num] [-vh]\n" );
    Abc_Print( -2, "\t         prints truth tables of outputs in hex notation\n" );
    Abc_Print( -2, "\t-O num : the index of first PO to print [default = %d]\n", iOutNum );
    Abc_Print( -2, "\t-R num : (optional) the number of outputs to extract [default = all]\n" );
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
int Abc_CommandAbc9Unate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManCheckUnateTest( Gia_Man_t * p, int fComputeAll, int fVerbose );
    int c, fComputeAll = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "avh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fComputeAll ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Unate(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManCheckUnateTest( pAbc->pGia, fComputeAll, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &unate [-avh]\n" );
    Abc_Print( -2, "\t         prints info about unatements of CO funcs in terms of CI vars\n" );
    Abc_Print( -2, "\t-a     : toggle using efficient computation for all pairs [default = %s]\n", fComputeAll? "yes": "no" );
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
int Abc_CommandAbc9Show( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Vec_Int_t * vBold = NULL;
    int c, fAdders = 0, fFadds = 0, fPath = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "afph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAdders ^= 1;
            break;
        case 'f':
            fFadds ^= 1;
            break;
        case 'p':
            fPath ^= 1;
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
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Show(): Cannot show GIA with barrier buffers.\n" );
        return 1;
    }
    if ( !fAdders && Gia_ManHasMapping(pAbc->pGia) )
    {
        vBold = Vec_IntAlloc( 100 );
        Gia_ManForEachLut( pAbc->pGia, c )
            Vec_IntPush( vBold, c );
    }
    Gia_ManShow( pAbc->pGia, vBold, fAdders, fFadds, fPath );
    Vec_IntFreeP( &vBold );
    return 0;

usage:
    Abc_Print( -2, "usage: &show [-afph]\n" );
    Abc_Print( -2, "\t        shows the current GIA using GSView\n" );
    Abc_Print( -2, "\t-a    : toggle visualazing adders [default = %s]\n", fAdders? "yes": "no" );
    Abc_Print( -2, "\t-f    : toggle showing only full-adders with \"-a\" [default = %s]\n", fFadds? "yes": "no" );
    Abc_Print( -2, "\t-p    : toggle showing the critical path of a LUT mapping [default = %s]\n", fPath? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Struct( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManTestStruct( Gia_Man_t * p );
    int c, fVerbose;
    // set defaults
    fVerbose   = 0;
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
        Abc_Print( -1, "Abc_CommandAbc9Struct(): There is no AIG to map.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Struct(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    if ( Gia_ManLutSizeMax(pAbc->pGia) >= 8 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Struct(): Can only handle nodes with less than 8 inputs.\n" );
        return 1;
    }
    Gia_ManTestStruct( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &struct [-vh]\n" );
    Abc_Print( -2, "\t           checks decomposition structures of the current mapping\n" );
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
int Abc_CommandAbc9PrintPath( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManPrintPath( Gia_Man_t * p, int nPaths, int fVerbose, int fSummary );
    int c, nPaths = 10, fVerbose = 0, fSummary = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nPaths = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPaths < 1 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSummary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PrintPath(): There is no AIG.\n" );
        return 0;
    }
    Gia_ManPrintPath( pAbc->pGia, nPaths, fVerbose, fSummary );
    return 0;

usage:
    Abc_Print( -2, "usage: &print_path [-N num] [-vsh]\n" );
    Abc_Print( -2, "\t          prints longest combinational paths between sequential endpoints\n" );
    Abc_Print( -2, "\t-N num  : number of path groups to print [default = %d]\n", nPaths );
    Abc_Print( -2, "\t-v      : toggle printing one AIG path for each path group [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-s      : toggle printing endpoint category summary [default = %s]\n", fSummary? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
