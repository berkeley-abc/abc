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
#include "fpga.h"
#include "if.h"
#include "res.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandPrintStats     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintExdc      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintIo        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLatch     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFanio     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintMffc      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFactor    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLevel     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSupport   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSymms     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintUnate     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintAuto      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintKMap      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintGates     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSharing   ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandShow           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowBdd        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowCut        ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCollapse       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandStrash         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBalance        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMulti          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRenode         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCleanup        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSweep          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFastExtract    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDisjoint       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMfs            ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandRewrite        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRefactor       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRestructure    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubstitute   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRr             ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandLogic          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandComb           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDemiter        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrPos          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAndPos         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAppend         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFrames         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSop            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBdd            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAig            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandReorder        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrder          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxes          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtSeqDcs      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneOutput      ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneNode        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShortNames     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcFree       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcGet        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcSet        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCut            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEspresso       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGen            ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandXyz            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDouble         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTest           ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandIStrash        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandICut           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewrite       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewriteSeq    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIResyn         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandISat           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIFraig         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIProve         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandHaig           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMini           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc            ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFraig          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigTrust     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigStore     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigRestore   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigClean     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigSweep     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigDress     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandMap            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnmap          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAttach         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoice    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoiceLut ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFpga           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFpgaFast       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIf             ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandScut           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInit           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPipe           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeq            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnseq          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRetime         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqFpga        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqMap         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqCleanup     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCycle          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandXsim           ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCec            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSec            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSat            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandProve          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDebug          ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandTraceStart     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTraceCheck     ( Abc_Frame_t * pAbc, int argc, char ** argv );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Init( Abc_Frame_t * pAbc )
{
//    Abc_NtkBddImplicationTest();

    Cmd_CommandAdd( pAbc, "Printing",     "print_stats",   Abc_CommandPrintStats,       0 ); 
    Cmd_CommandAdd( pAbc, "Printing",     "print_exdc",    Abc_CommandPrintExdc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_io",      Abc_CommandPrintIo,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_latch",   Abc_CommandPrintLatch,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_fanio",   Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_mffc",    Abc_CommandPrintMffc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_factor",  Abc_CommandPrintFactor,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_level",   Abc_CommandPrintLevel,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_supp",    Abc_CommandPrintSupport,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_symm",    Abc_CommandPrintSymms,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_unate",   Abc_CommandPrintUnate,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_auto",    Abc_CommandPrintAuto,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_kmap",    Abc_CommandPrintKMap,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_gates",   Abc_CommandPrintGates,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_sharing", Abc_CommandPrintSharing,     0 );

    Cmd_CommandAdd( pAbc, "Printing",     "show",          Abc_CommandShow,             0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_bdd",      Abc_CommandShowBdd,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_cut",      Abc_CommandShowCut,          0 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "collapse",      Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "strash",        Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "balance",       Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "multi",         Abc_CommandMulti,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "renode",        Abc_CommandRenode,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cleanup",       Abc_CommandCleanup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "sweep",         Abc_CommandSweep,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fx",            Abc_CommandFastExtract,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "dsd",           Abc_CommandDisjoint,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mfs",           Abc_CommandMfs,              1 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "rewrite",       Abc_CommandRewrite,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "refactor",      Abc_CommandRefactor,         1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "restructure",   Abc_CommandRestructure,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub",         Abc_CommandResubstitute,     1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "rr",            Abc_CommandRr,               1 );

    Cmd_CommandAdd( pAbc, "Various",      "logic",         Abc_CommandLogic,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "comb",          Abc_CommandComb,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "miter",         Abc_CommandMiter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "demiter",       Abc_CommandDemiter,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "orpos",         Abc_CommandOrPos,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "andpos",        Abc_CommandAndPos,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "append",        Abc_CommandAppend,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "frames",        Abc_CommandFrames,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "sop",           Abc_CommandSop,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "bdd",           Abc_CommandBdd,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "aig",           Abc_CommandAig,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "reorder",       Abc_CommandReorder,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "order",         Abc_CommandOrder,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "muxes",         Abc_CommandMuxes,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "ext_seq_dcs",   Abc_CommandExtSeqDcs,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "cone",          Abc_CommandOneOutput,        1 );
    Cmd_CommandAdd( pAbc, "Various",      "node",          Abc_CommandOneNode,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "short_names",   Abc_CommandShortNames,       0 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_free",     Abc_CommandExdcFree,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_get",      Abc_CommandExdcGet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_set",      Abc_CommandExdcSet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "cut",           Abc_CommandCut,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "espresso",      Abc_CommandEspresso,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "gen",           Abc_CommandGen,              0 );
//    Cmd_CommandAdd( pAbc, "Various",      "xyz",           Abc_CommandXyz,              1 );
    Cmd_CommandAdd( pAbc, "Various",      "double",        Abc_CommandDouble,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "test",          Abc_CommandTest,             0 );

    Cmd_CommandAdd( pAbc, "New AIG",      "istrash",       Abc_CommandIStrash,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "icut",          Abc_CommandICut,             0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irw",           Abc_CommandIRewrite,         1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irws",          Abc_CommandIRewriteSeq,      1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "iresyn",        Abc_CommandIResyn,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "isat",          Abc_CommandISat,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "ifraig",        Abc_CommandIFraig,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "iprove",        Abc_CommandIProve,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "haig",          Abc_CommandHaig,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "mini",          Abc_CommandMini,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "bmc",           Abc_CommandBmc,              0 );

    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig",         Abc_CommandFraig,            1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_trust",   Abc_CommandFraigTrust,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_store",   Abc_CommandFraigStore,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_restore", Abc_CommandFraigRestore,     1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_clean",   Abc_CommandFraigClean,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_sweep",   Abc_CommandFraigSweep,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "dress",         Abc_CommandFraigDress,       1 );

    Cmd_CommandAdd( pAbc, "SC mapping",   "map",           Abc_CommandMap,              1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "unmap",         Abc_CommandUnmap,            1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "attach",        Abc_CommandAttach,           1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "sc",            Abc_CommandSuperChoice,      1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "scl",           Abc_CommandSuperChoiceLut,   1 );

    Cmd_CommandAdd( pAbc, "FPGA mapping", "fpga",          Abc_CommandFpga,             1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "ffpga",         Abc_CommandFpgaFast,         1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "if",            Abc_CommandIf,               1 );

//    Cmd_CommandAdd( pAbc, "Sequential",   "scut",          Abc_CommandScut,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "init",          Abc_CommandInit,             1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "pipe",          Abc_CommandPipe,             1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "seq",           Abc_CommandSeq,              1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "unseq",         Abc_CommandUnseq,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "retime",        Abc_CommandRetime,           1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "sfpga",         Abc_CommandSeqFpga,          1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "smap",          Abc_CommandSeqMap,           1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "ssweep",        Abc_CommandSeqSweep,         1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "scleanup",      Abc_CommandSeqCleanup,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cycle",         Abc_CommandCycle,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "xsim",          Abc_CommandXsim,             0 );

    Cmd_CommandAdd( pAbc, "Verification", "cec",           Abc_CommandCec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "sec",           Abc_CommandSec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "sat",           Abc_CommandSat,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "prove",         Abc_CommandProve,            1 );
    Cmd_CommandAdd( pAbc, "Verification", "debug",         Abc_CommandDebug,            0 );

//    Cmd_CommandAdd( pAbc, "Verification", "trace_start",   Abc_CommandTraceStart,       0 );
//    Cmd_CommandAdd( pAbc, "Verification", "trace_check",   Abc_CommandTraceCheck,       0 );

//    Rwt_Man4ExploreStart();
//    Map_Var3Print();
//    Map_Var4Test();

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fShort  = 1;
    fFactor = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sfh" ) ) != EOF )
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
        fprintf( Abc_FrameReadErr(pAbc), "Empty network.\n" );
        return 1;
    }
    Abc_NtkPrintStats( pOut, pNtk, fFactor );
    return 0;

usage:
    fprintf( pErr, "usage: print_stats [-fh]\n" );
    fprintf( pErr, "\t        prints the network statistics\n" );
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
int Abc_CommandPrintExdc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    double Percentage;
    bool fShort;
    int c;
    int fPrintDc;

    extern double Abc_NtkSpacePercentage( Abc_Obj_t * pNode );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( Abc_FrameReadErr(pAbc), "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        fprintf( Abc_FrameReadErr(pAbc), "Network has no EXDC.\n" );
        return 1;
    }

    if ( fPrintDc )
    {
        if ( !Abc_NtkIsStrash(pNtk->pExdc) )
        {
            pNtkTemp = Abc_NtkStrash(pNtk->pExdc, 0, 0);
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtkTemp, 0) ) );
            Abc_NtkDelete( pNtkTemp );
        }
        else
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtk->pExdc, 0) ) );

        printf( "EXDC network statistics: " );
        printf( "(" );
        if ( Percentage > 0.05 && Percentage < 99.95 )
            printf( "%.2f", Percentage );
        else if ( Percentage > 0.000005 && Percentage < 99.999995 )
            printf( "%.6f", Percentage );
        else
            printf( "%f", Percentage );
        printf( " %% don't-cares)\n" );
    }
    else
        printf( "EXDC network statistics: \n" );
    Abc_NtkPrintStats( pOut, pNtk->pExdc, 0 );
    return 0;

usage:
    fprintf( pErr, "usage: print_exdc [-dh]\n" );
    fprintf( pErr, "\t        prints the EXDC network statistics\n" );
    fprintf( pErr, "\t-d    : toggles printing don't-care percentage [default = %s]\n", fPrintDc? "yes": "no" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
int Abc_CommandPrintMffc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern void Abc_NtkPrintMffc( FILE * pFile, Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // print the nodes
    Abc_NtkPrintMffc( pOut, pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_mffc [-h]\n" );
    fprintf( pErr, "\t        prints the MFFC of each node in the network\n" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
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
    int fListNodes;
    int fProfile;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fListNodes = 0;
    fProfile   = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fListNodes ^= 1;
            break;
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

    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintLevel( pOut, pNode );
        return 0;
    }
    // process all COs
    Abc_NtkPrintLevel( pOut, pNtk, fProfile, fListNodes );
    return 0;

usage:
    fprintf( pErr, "usage: print_level [-nph] <node>\n" );
    fprintf( pErr, "\t        prints information about node level and cone size\n" );
    fprintf( pErr, "\t-n    : toggles printing nodes by levels [default = %s]\n", fListNodes? "yes": "no" );
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
    int fStruct;
    int fVerbose;
    extern Vec_Ptr_t * Sim_ComputeFunSupp( Abc_Ntk_t * pNtk, int fVerbose );
    extern void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fStruct = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fStruct ^= 1;
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

    // print support information
    if ( fStruct )
    {
        Abc_NtkPrintStrSupports( pNtk );
        return 0;
    }

    if ( !Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "This command works only for combinational networks (run \"comb\").\n" );
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
    fprintf( pErr, "usage: print_supp [-svh]\n" );
    fprintf( pErr, "\t        prints the supports of the CO nodes\n" );
    fprintf( pErr, "\t-s    : toggle printing structural support only [default = %s].\n", fStruct? "yes": "no" );  
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
    int fReorder;
    int fVerbose;
    extern void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fReorder, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "This command works only for combinational networks (run \"comb\").\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    fprintf( pErr, "usage: print_symm [-bnrvh]\n" );
    fprintf( pErr, "\t         computes symmetries of the PO functions\n" );
    fprintf( pErr, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );  
    fprintf( pErr, "\t-n     : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );  
    fprintf( pErr, "\t-r     : enable dynamic BDD variable reordering [default = %s].\n", fReorder? "yes": "no" );  
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
int Abc_CommandPrintUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fUseBdds;
    int fUseNaive;
    int fVerbose;
    extern void Abc_NtkPrintUnate( Abc_Ntk_t * pNtk, int fUseBdds, int fUseNaive, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    Abc_NtkPrintUnate( pNtk, fUseBdds, fUseNaive, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: print_unate [-bnvh]\n" );
    fprintf( pErr, "\t         computes unate variables of the PO functions\n" );
    fprintf( pErr, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );  
    fprintf( pErr, "\t-n     : toggle naive BDD-based computation [default = %s].\n", fUseNaive? "yes": "no" );  
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
int Abc_CommandPrintAuto( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int Output;
    int fNaive;
    int fVerbose;
    extern void Abc_NtkAutoPrint( Abc_Ntk_t * pNtk, int Output, int fNaive, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-O\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }


    Abc_NtkAutoPrint( pNtk, Output, fNaive, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: print_auto [-O num] [-nvh]\n" );
    fprintf( pErr, "\t         computes autosymmetries of the PO functions\n" );
    fprintf( pErr, "\t-O num : (optional) the 0-based number of the output [default = all]\n");
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
int Abc_CommandPrintKMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c;
    int fUseRealNames;

    extern void Abc_NodePrintKMap( Abc_Obj_t * pNode, int fUseRealNames );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Visualizing Karnaugh map works for BDD logic networks (run \"bdd\").\n" );
        return 1;
    }
    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            fprintf( pErr, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    Abc_NodePrintKMap( pNode, fUseRealNames );
    return 0;

usage:
    fprintf( pErr, "usage: print_kmap [-nh] <node>\n" );
    fprintf( pErr, "          shows the truth table of the node\n" );
    fprintf( pErr, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    fprintf( pErr, "\tnode  : the node to consider (default = the driver of the first PO)\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintGates( Abc_Ntk_t * pNtk, int fUseLibrary );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkHasAig(pNtk) )
    {
        fprintf( pErr, "Printing gates does not work for AIGs and sequential AIGs.\n" );
        return 1;
    }

    Abc_NtkPrintGates( pNtk, fUseLibrary );
    return 0;

usage:
    fprintf( pErr, "usage: print_gates [-lh]\n" );
    fprintf( pErr, "\t        prints statistics about gates used in the network\n" );
    fprintf( pErr, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintSharing( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    Abc_NtkPrintSharing( pNtk );
    return 0;

usage:
    fprintf( pErr, "usage: print_sharing [-h]\n" );
    fprintf( pErr, "\t        prints the number of shared nodes in the TFI cones of the COs\n" );
//    fprintf( pErr, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fSeq;
    int fGateNames;
    int fUseReverse;
    extern void Abc_NtkShow( Abc_Ntk_t * pNtk, int fGateNames, int fSeq, int fUseReverse );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fSeq        = 0;
    fGateNames  = 0;
    fUseReverse = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rsgh" ) ) != EOF )
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
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    Abc_NtkShow( pNtk, fGateNames, fSeq, fUseReverse );
    return 0;

usage:
    fprintf( pErr, "usage: show [-srgh]\n" );
    fprintf( pErr, "       visualizes the network structure using DOT and GSVIEW\n" );
#ifdef WIN32
    fprintf( pErr, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    fprintf( pErr, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    fprintf( pErr, "\t-s    : toggles visualization of sequential networks [default = %s].\n", fSeq? "yes": "no" );  
    fprintf( pErr, "\t-r    : toggles ordering nodes in reverse order [default = %s].\n", fUseReverse? "yes": "no" );  
    fprintf( pErr, "\t-g    : toggles printing gate names for mapped network [default = %s].\n", fGateNames? "yes": "no" );  
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
    extern void Abc_NodeShowBdd( Abc_Obj_t * pNode );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Visualizing BDDs can only be done for logic BDD networks (run \"bdd\").\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            fprintf( pErr, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
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
    fprintf( pErr, "\tnode  : the node to consider [default = the driver of the first PO]\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Visualizing cuts only works for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
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
int Abc_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fVerbose;
    int fBddSizeMax;
    int fDualRail;
    int fReorder;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose = 1;
    fReorder = 1;
    fDualRail = 0;
    fBddSizeMax = 50000000;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Brdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            fBddSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fBddSizeMax < 0 ) 
                goto usage;
            break;
        case 'd':
            fDualRail ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'r':
            fReorder ^= 1;
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
        fprintf( pErr, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fVerbose );
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
    fprintf( pErr, "usage: collapse [-B num] [-rdvh]\n" );
    fprintf( pErr, "\t          collapses the network by constructing global BDDs\n" );
    fprintf( pErr, "\t-B num  : limit on live BDD nodes during collapsing [default = %d]\n", fBddSizeMax );
    fprintf( pErr, "\t-r      : toggles dynamic variable reordering [default = %s]\n", fReorder? "yes": "no" );
    fprintf( pErr, "\t-d      : toggles dual-rail collapsing mode [default = %s]\n", fDualRail? "yes": "no" );
    fprintf( pErr, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    fprintf( pErr, "\t-h      : print the command usage\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fAllNodes = 0;
    fCleanup  = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ach" ) ) != EOF )
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
    bool fDuplicate;
    bool fSelective;
    bool fUpdateLevel;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDuplicate   = 0;
    fSelective   = 0;
    fUpdateLevel = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ldsh" ) ) != EOF )
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
        pNtkRes = Abc_NtkBalance( pNtk, fDuplicate, fSelective, fUpdateLevel );
    }
    else
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtkTemp == NULL )
        {
            fprintf( pErr, "Strashing before balancing has failed.\n" );
            return 1;
        }
        pNtkRes = Abc_NtkBalance( pNtkTemp, fDuplicate, fSelective, fUpdateLevel );
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
    fprintf( pErr, "usage: balance [-ldsh]\n" );
    fprintf( pErr, "\t        transforms the current network into a well-balanced AIG\n" );
    fprintf( pErr, "\t-l    : toggle minimizing the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    fprintf( pErr, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    fprintf( pErr, "\t-s    : toggle duplication on the critical paths [default = %s]\n", fSelective? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nThresh, nFaninMax, c;
    int fCnf;
    int fMulti;
    int fSimple;
    int fFactor;
    extern Abc_Ntk_t * Abc_NtkMulti( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple, int fFactor );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-T\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkMulti( pNtk, nThresh, nFaninMax, fCnf, fMulti, fSimple, fFactor );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: multi [-T num] [-F num] [-msfch]\n" );
    fprintf( pErr, "\t          transforms an AIG into a logic network by creating larger nodes\n" );
    fprintf( pErr, "\t-F num  : the maximum fanin size after renoding [default = %d]\n", nFaninMax );
    fprintf( pErr, "\t-T num  : the threshold for AIG node duplication [default = %d]\n", nThresh );
    fprintf( pErr, "\t          (an AIG node is the root of a new node after renoding\n" );
    fprintf( pErr, "\t          if this leads to duplication of no more than %d AIG nodes,\n", nThresh );
    fprintf( pErr, "\t          that is, if [(numFanouts(Node)-1) * size(MFFC(Node))] <= %d)\n", nThresh );
    fprintf( pErr, "\t-m      : creates multi-input AND graph [default = %s]\n", fMulti? "yes": "no" );
    fprintf( pErr, "\t-s      : creates a simple AIG (no renoding) [default = %s]\n", fSimple? "yes": "no" );
    fprintf( pErr, "\t-f      : creates a factor-cut network [default = %s]\n", fFactor? "yes": "no" );
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
int Abc_CommandRenode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nLutSize, nCutsMax, c;
    int nFlowIters, nAreaIters;
    int fArea;
    int fUseBdds;
    int fUseSops;
    int fUseCnfs;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkRenode( Abc_Ntk_t * pNtk, int nLutSize, int nCutsMax, int nFlowIters, int nAreaIters, int fArea, int fUseBdds, int fUseSops, int fUseCnfs, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nLutSize   =  8;
    nCutsMax   =  5;
    nFlowIters =  1;
    nAreaIters =  1;
    fArea      =  0;
    fUseBdds   =  0;
    fUseSops   =  0;
    fUseCnfs   =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFAabscvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-F\" should be followed by a positive integer.\n" );
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
                fprintf( pErr, "Command line switch \"-A\" should be followed by a positive integer.\n" );
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
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( fUseBdds && fUseSops || fUseBdds && fUseCnfs || fUseSops && fUseCnfs )
    {
        fprintf( pErr, "Cannot optimize two parameters at the same time.\n" );
        return 1;
    }

    if ( nLutSize < 3 || nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        fprintf( pErr, "Incorrect LUT size (%d).\n", nLutSize );
        return 1;
    }

    if ( nCutsMax < 2 || nCutsMax >= (1<<12) )
    {
        fprintf( pErr, "Incorrect number of cuts.\n" );
        return 1;
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
    pNtkRes = Abc_NtkRenode( pNtk, nLutSize, nCutsMax, nFlowIters, nAreaIters, fArea, fUseBdds, fUseSops, fUseCnfs, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: renode [-K num] [-C num] [-F num] [-A num] [-sbcav]\n" );
    fprintf( pErr, "\t          transforms the AIG into a logic network with larger nodes\n" );
    fprintf( pErr, "\t          while minimizing the number of FF literals of the node SOPs\n" );
    fprintf( pErr, "\t-K num  : the max cut size for renoding (2 < num < %d) [default = %d]\n", IF_MAX_FUNC_LUTSIZE+1, nLutSize );
    fprintf( pErr, "\t-C num  : the max number of cuts used at a node (1 < num < 2^12) [default = %d]\n", nCutsMax );
    fprintf( pErr, "\t-F num  : the number of area flow recovery iterations (num >= 0) [default = %d]\n", nFlowIters );
    fprintf( pErr, "\t-A num  : the number of exact area recovery iterations (num >= 0) [default = %d]\n", nAreaIters );
    fprintf( pErr, "\t-s      : toggles minimizing SOP cubes instead of FF lits [default = %s]\n", fUseSops? "yes": "no" );
    fprintf( pErr, "\t-b      : toggles minimizing BDD nodes instead of FF lits [default = %s]\n", fUseBdds? "yes": "no" );
    fprintf( pErr, "\t-c      : toggles minimizing CNF clauses instead of FF lits [default = %s]\n", fUseCnfs? "yes": "no" );
    fprintf( pErr, "\t-a      : toggles area-oriented mapping [default = %s]\n", fArea? "yes": "no" );
    fprintf( pErr, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Cleanup cannot be performed on the AIG.\n" );
        return 1;
    }
    // modify the current network
    Abc_NtkCleanup( pNtk, 1 );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "The classical (SIS-like) sweep can only be performed on a logic network.\n" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
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
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "LNsdzcvh")) != EOF ) 
    {
        switch (c) 
        {
            case 'L':
                if ( globalUtilOptind >= argc )
                {
                    fprintf( pErr, "Command line switch \"-L\" should be followed by an integer.\n" );
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
                    fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nNodesExt = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
            fprintf( pErr, "This command is only applicable to logic BDD networks (run \"bdd\").\n" );
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
int Abc_CommandMfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Res_Par_t Pars, * pPars = &Pars;
    int c;

//    printf( "Implementation of this command is not finished.\n" );
//    return 1;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    pPars->nWindow      = 62;
    pPars->nCands       =  5;
    pPars->nSimWords    =  4;
    pPars->fArea        =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WSavwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWindow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWindow < 1 || pPars->nWindow > 99 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSimWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSimWords < 1 || pPars->nSimWords > 256 ) 
                goto usage;
            break;
        case 'a':
            pPars->fArea ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkResynthesize( pNtk, pPars ) )
    {
        fprintf( pErr, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: mfs [-W <NM>] [-S <num>] [-avwh]\n" );
    fprintf( pErr, "\t           performs resubstitution-based resynthesis with don't-cares\n" );
    fprintf( pErr, "\t-W <NM>  : Fanin/Fanout levels (NxM) of the window (00 <= NM <= 99) [default = %d%d]\n", pPars->nWindow/10, pPars->nWindow%10 );
    fprintf( pErr, "\t-S <num> : the number of simulation words (1 <= n <= 256) [default = %d]\n", pPars->nSimWords );
    fprintf( pErr, "\t-a       : toggle optimization for area only [default = %s]\n", pPars->fArea? "yes": "no" );
    fprintf( pErr, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-w       : toggle printout subgraph statistics [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    fprintf( pErr, "\t-h       : print the command usage\n");
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
    bool fUpdateLevel;
    bool fPrecompute;
    bool fUseZeros;
    bool fVerbose;
    bool fVeryVerbose;
    // external functions
    extern void Rwr_Precompute();

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUpdateLevel = 1;
    fPrecompute  = 0;
    fUseZeros    = 0;
    fVerbose     = 0;
    fVeryVerbose = 0;
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
    if ( !Abc_NtkRewrite( pNtk, fUpdateLevel, fUseZeros, fVerbose, fVeryVerbose ) )
    {
        fprintf( pErr, "Rewriting has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: rewrite [-lzvwh]\n" );
    fprintf( pErr, "\t         performs technology-independent rewriting of the AIG\n" );
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-w     : toggle printout subgraph statistics [default = %s]\n", fVeryVerbose? "yes": "no" );
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
    bool fUpdateLevel;
    bool fUseZeros;
    bool fUseDcs;
    bool fVerbose;
    extern int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, bool fUpdateLevel, bool fUseZeros, bool fUseDcs, bool fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NClzdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
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
    if ( !Abc_NtkRefactor( pNtk, nNodeSizeMax, nConeSizeMax, fUpdateLevel, fUseZeros, fUseDcs, fVerbose ) )
    {
        fprintf( pErr, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: refactor [-N num] [-C num] [-lzdvh]\n" );
    fprintf( pErr, "\t         performs technology-independent refactoring of the AIG\n" );
    fprintf( pErr, "\t-N num : the max support of the collapsed node [default = %d]\n", nNodeSizeMax );  
    fprintf( pErr, "\t-C num : the max support of the containing cone [default = %d]\n", nConeSizeMax );  
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandRestructure( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nCutsMax;
    bool fUpdateLevel;
    bool fUseZeros;
    bool fVerbose;
    extern int Abc_NtkRestructure( Abc_Ntk_t * pNtk, int nCutsMax, bool fUpdateLevel, bool fUseZeros, bool fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < 4 || nCutsMax > CUT_SIZE_MAX )
    {
        fprintf( pErr, "Can only compute the cuts for %d <= K <= %d.\n", 4, CUT_SIZE_MAX );
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
    if ( !Abc_NtkRestructure( pNtk, nCutsMax, fUpdateLevel, fUseZeros, fVerbose ) )
    {
        fprintf( pErr, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: restructure [-K num] [-lzvh]\n" );
    fprintf( pErr, "\t         performs technology-independent restructuring of the AIG\n" );
    fprintf( pErr, "\t-K num : the max cut size (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, nCutsMax );  
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandResubstitute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int RS_CUT_MIN =  4;
    int RS_CUT_MAX = 16;
    int c;
    int nCutsMax;
    int nNodesMax;
    int nLevelsOdc;
    bool fUpdateLevel;
    bool fUseZeros;
    bool fVerbose;
    bool fVeryVerbose;
    extern int Abc_NtkResubstitute( Abc_Ntk_t * pNtk, int nCutsMax, int nNodesMax, int nLevelsOdc, bool fUpdateLevel, bool fVerbose, bool fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fVerbose     =  0;
    fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNFlzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
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
            fUseZeros ^= 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < RS_CUT_MIN || nCutsMax > RS_CUT_MAX )
    {
        fprintf( pErr, "Can only compute cuts for %d <= K <= %d.\n", RS_CUT_MIN, RS_CUT_MAX );
        return 1;
    }
    if ( nNodesMax < 0 || nNodesMax > 3 )
    {
        fprintf( pErr, "Can only resubstitute at most 3 nodes.\n" );
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
    if ( !Abc_NtkResubstitute( pNtk, nCutsMax, nNodesMax, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose ) )
    {
        fprintf( pErr, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: resub [-K num] [-N num] [-F num] [-lzvwh]\n" );
    fprintf( pErr, "\t         performs technology-independent restructuring of the AIG\n" );
    fprintf( pErr, "\t-K num : the max cut size (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );  
    fprintf( pErr, "\t-N num : the max number of nodes to add (0 <= num <= 3) [default = %d]\n", nNodesMax );  
    fprintf( pErr, "\t-F num : the number of fanout levels for ODC computation [default = %d]\n", nLevelsOdc );  
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-w     : toggle verbose printout of ODC computation [default = %s]\n", fVeryVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c, Window;
    int nFaninLevels;
    int nFanoutLevels;
    int fUseFanouts;
    int fVerbose;
    extern int Abc_NtkRR( Abc_Ntk_t * pNtk, int nFaninLevels, int nFanoutLevels, int fUseFanouts, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-W\" should be followed by an integer.\n" );
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
    if ( !Abc_NtkRR( pNtk, nFaninLevels, nFanoutLevels, fUseFanouts, fVerbose ) )
    {
        fprintf( pErr, "Redundancy removal has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: rr [-W NM] [-fvh]\n" );
    fprintf( pErr, "\t         removes combinational redundancies in the current network\n" );
    fprintf( pErr, "\t-W NM  : window size: TFI (N) and TFO (M) logic levels [default = %d%d]\n", nFaninLevels, nFanoutLevels );
    fprintf( pErr, "\t-f     : toggle RR w.r.t. fanouts [default = %s]\n", fUseFanouts? "yes": "no" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        fprintf( pErr, "This command is only applicable to strashed networks.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkAigToLogicSop( pNtk );
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
    fprintf( pErr, "\t        transforms an AIG into a logic network with SOPs\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandComb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "The network is already combinational.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_NtkMakeComb( pNtkRes );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: comb [-h]\n" );
    fprintf( pErr, "\t        makes the current network combinational by replacing latches by PI/PO pairs\n" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fComb  = 1;
    fCheck = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
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

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
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
int Abc_CommandDemiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;//, * pNtkRes;
    int fComb;
    int c;
    extern int Abc_NtkDemiter( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
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

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "The network is not strashed.\n" );
        return 1;
    }

    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        fprintf( pErr, "The network is not a miter.\n" );
        return 1;
    }

    if ( !Abc_NodeIsExorType(Abc_ObjFanin0(Abc_NtkPo(pNtk,0))) )
    {
        fprintf( pErr, "The miter's PO is not an EXOR.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkDemiter( pNtk ) )
    {
        fprintf( pErr, "Demitering has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: demiter [-h]\n" );
    fprintf( pErr, "\t        removes topmost EXOR from the miter to create two POs\n" );
//    fprintf( pErr, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOrPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;//, * pNtkRes;
    int fComb;
    int c;
    extern int Abc_NtkCombinePos( Abc_Ntk_t * pNtk, int fAnd );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
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

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "The network is not strashed.\n" );
        return 1;
    }

    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        fprintf( pErr, "The network already has one PO.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) )
    {
        fprintf( pErr, "The miter has latches. ORing is not performed.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkCombinePos( pNtk, 0 ) )
    {
        fprintf( pErr, "ORing the POs has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: orpos [-h]\n" );
    fprintf( pErr, "\t        creates single-output miter by ORing the POs of the current network\n" );
//    fprintf( pErr, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAndPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;//, * pNtkRes;
    int fComb;
    int c;
    extern int Abc_NtkCombinePos( Abc_Ntk_t * pNtk, int fAnd );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
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

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "The network is not strashed.\n" );
        return 1;
    }

    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        fprintf( pErr, "The network already has one PO.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) )
    {
        fprintf( pErr, "The miter has latches. ORing is not performed.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkCombinePos( pNtk, 1 ) )
    {
        fprintf( pErr, "ANDing the POs has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: andpos [-h]\n" );
    fprintf( pErr, "\t        creates single-output miter by ANDing the POs of the current network\n" );
//    fprintf( pErr, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAppend( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk2;
    char * FileName;
    int fComb;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
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

    // get the second network
    if ( argc != globalUtilOptind + 1 )
    {
        fprintf( pErr, "The network to append is not given.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "The base network should be strashed for the appending to work.\n" );
        return 1;
    }

    // read the second network
    FileName = argv[globalUtilOptind];
    pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
    if ( pNtk2 == NULL )
        return 1;

    // check if the second network is combinational
    if ( Abc_NtkLatchNum(pNtk2) )
    {
        fprintf( pErr, "The second network has latches. Appending does not work for such networks.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkAppend( pNtk, pNtk2, 1 ) )
    {
        Abc_NtkDelete( pNtk2 );
        fprintf( pErr, "Appending the networks failed.\n" );
        return 1;
    }
    Abc_NtkDelete( pNtk2 );
    // sweep dangling logic
    Abc_AigCleanup( pNtk->pManFunc );
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: append [-h] <file>\n" );
    fprintf( pErr, "\t         appends a combinational network on top of the current network\n" );
//    fprintf( pErr, "\t-c     : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t<file> : file name with the second network\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fInitial = 0;
    nFrames  = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
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
    int fDirect;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fDirect = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDirect ^= 1;
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
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Converting to SOP is possible only for logic networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLogicToSop(pNtk, fDirect) )
    {
        fprintf( pErr, "Converting to SOP has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: sop [-dh]\n" );
    fprintf( pErr, "\t         converts node functions to SOP\n" );
    fprintf( pErr, "\t-d     : toggles using both phases or only positive [default = %s]\n", fDirect? "direct": "both" );  
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Converting to BDD is possible only for logic networks.\n" );
        return 1;
    }
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pOut, "The logic network is already in the BDD form.\n" );
        return 0;
    }
    if ( !Abc_NtkLogicToBdd(pNtk) )
    {
        fprintf( pErr, "Converting to BDD has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: bdd [-h]\n" );
    fprintf( pErr, "\t         converts node functions to BDD\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Converting to AIG is possible only for logic networks.\n" );
        return 1;
    }
    if ( Abc_NtkIsAigLogic(pNtk) )
    {
        fprintf( pOut, "The logic network is already in the AIG form.\n" );
        return 0;
    }
    if ( !Abc_NtkLogicToAig(pNtk) )
    {
        fprintf( pErr, "Converting to AIG has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: aig [-h]\n" );
    fprintf( pErr, "\t         converts node functions to AIG\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;
    extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        fprintf( pErr, "Variable reordering is possible when node functions are BDDs (run \"bdd\").\n" );
        return 1;
    }
    Abc_NtkBddReorder( pNtk, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: reorder [-vh]\n" );
    fprintf( pErr, "\t         reorders local functions of the nodes using sifting\n" );
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
int Abc_CommandOrder( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr, * pFile;
    Abc_Ntk_t * pNtk;
    char * pFileName;
    int c;
    int fReverse;
    int fVerbose;
    extern void Abc_NtkImplementCiOrder( Abc_Ntk_t * pNtk, char * pFileName, int fReverse, int fVerbose );
    extern void Abc_NtkFindCiOrder( Abc_Ntk_t * pNtk, int fReverse, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fReverse = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
//    if ( Abc_NtkLatchNum(pNtk) > 0 )
//    {
//        printf( "Currently this procedure does not work for sequential networks.\n" );
//        return 1;
//    }

    // if the var order file is given, implement this order
    pFileName = NULL;
    if ( argc == globalUtilOptind + 1 )
    {
        pFileName = argv[globalUtilOptind];
        pFile = fopen( pFileName, "r" );
        if ( pFile == NULL )
        {
            fprintf( pErr, "Cannot open file \"%s\" with the BDD variable order.\n", pFileName );
            return 1;
        }
        fclose( pFile );
    }
    if ( pFileName )
        Abc_NtkImplementCiOrder( pNtk, pFileName, fReverse, fVerbose );
    else
        Abc_NtkFindCiOrder( pNtk, fReverse, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: order [-rvh] <file>\n" );
    fprintf( pErr, "\t         computes a good static CI variable order\n" );
    fprintf( pErr, "\t-r     : toggle reverse ordering [default = %s]\n", fReverse? "yes": "no" );  
    fprintf( pErr, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t<file> : (optional) file with the given variable order\n" );  
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
int Abc_CommandExtSeqDcs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;
    extern int Abc_NtkExtractSequentialDcs( Abc_Ntk_t * pNet, bool fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( stdout, "Extracting sequential don't-cares works only for AIGs (run \"strash\").\n" );
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
    Abc_Obj_t * pNode, * pNodeCo;
    int c;
    int fUseAllCis;
    int fUseMffc;
    int Output;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseAllCis = 0;
    fUseMffc = 0;
    Output = -1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Omah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            Output = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Output < 0 ) 
                goto usage;
            break;
        case 'm':
            fUseMffc ^= 1;
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

    if ( argc > globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNodeCo = NULL;
    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, pNode, argv[globalUtilOptind] );
        else
            pNtkRes = Abc_NtkCreateCone( pNtk, pNode, argv[globalUtilOptind], fUseAllCis );
    }
    else
    {
        if ( Output == -1 )
        {
            fprintf( pErr, "The node is not specified.\n" );
            return 1;
        }
        if ( Output >= Abc_NtkCoNum(pNtk) )
        {
            fprintf( pErr, "The 0-based output number (%d) is larger than the number of outputs (%d).\n", Output, Abc_NtkCoNum(pNtk) );
            return 1;
        }
        pNodeCo = Abc_NtkCo( pNtk, Output );
        if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo) );
        else
            pNtkRes = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo), fUseAllCis );
    }
    if ( pNodeCo && Abc_ObjFaninC0(pNodeCo) )
        printf( "The extracted cone represents the complement function of the CO.\n" );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Writing the logic cone of one node has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: cone [-O num] [-amh] <name>\n" );
    fprintf( pErr, "\t         replaces the current network by one logic cone\n" );
    fprintf( pErr, "\t-a     : toggle writing all CIs or structral support only [default = %s]\n", fUseAllCis? "all": "structural" );
    fprintf( pErr, "\t-m     : toggle writing only MFFC or complete TFI cone [default = %s]\n", fUseMffc? "MFFC": "TFI cone" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t-O num : (optional) the 0-based number of the CO to extract\n");
    fprintf( pErr, "\tname   : (optional) the name of the node to extract\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Currently can only be applied to a logic network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        fprintf( pErr, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        fprintf( pErr, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
        return 1;
    }

    pNtkRes = Abc_NtkCreateFromNode( pNtk, pNode );
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
    fprintf( pErr, "usage: node [-h] <name>\n" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
int Abc_CommandExdcFree( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        fprintf( pErr, "The network has no EXDC.\n" );
        return 1;
    }

    Abc_NtkDelete( pNtk->pExdc );
    pNtk->pExdc = NULL;

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: exdc_free [-h]\n" );
    fprintf( pErr, "\t         frees the EXDC network of the current network\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExdcGet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        fprintf( pErr, "The network has no EXDC.\n" );
        return 1;
    }

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk->pExdc );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: exdc_get [-h]\n" );
    fprintf( pErr, "\t         replaces the current network by the EXDC of the current network\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExdcSet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr, * pFile;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    char * FileName;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
    if ( pNtkNew == NULL )
    {
        fprintf( pAbc->Err, "Reading network from file has failed.\n" );
        return 1;
    }

    // replace the EXDC
    if ( pNtk->pExdc )
    {
        Abc_NtkDelete( pNtk->pExdc );
        pNtk->pExdc = NULL;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    pNtkRes->pExdc = pNtkNew;

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: exdc_set [-h] <file>\n" );
    fprintf( pErr, "\t         sets the network from file as EXDC for the current network\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t<file> : file with the new EXDC network\n");
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
    Cut_Oracle_t * pCutOracle;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fOracle;
    extern Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );
    extern void Abc_NtkCutsOracle( Abc_Ntk_t * pNtk, Cut_Oracle_t * pCutOracle );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fOracle = 0;
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 1000;  // the max number of cuts kept at a node
    pParams->fTruth    = 0;     // compute truth tables
    pParams->fFilter   = 1;     // filter dominated cuts
    pParams->fDrop     = 0;     // drop cuts on the fly
    pParams->fDag      = 0;     // compute DAG cuts
    pParams->fTree     = 0;     // compute tree cuts
    pParams->fGlobal   = 0;     // compute global cuts
    pParams->fLocal    = 0;     // compute local cuts
    pParams->fFancy    = 0;     // compute something fancy
    pParams->fMap      = 0;     // compute mapping delay
    pParams->fVerbose  = 0;     // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMtfdxyglzmvoh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-M\" should be followed by an integer.\n" );
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
        case 'm':
            pParams->fMap ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'o':
            fOracle ^= 1;
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
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        fprintf( pErr, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }
    if ( pParams->fDag && pParams->fTree )
    {
        fprintf( pErr, "Cannot compute both DAG cuts and tree cuts at the same time.\n" );
        return 1;
    }

    if ( fOracle )
        pParams->fRecord = 1;
    pCutMan = Abc_NtkCuts( pNtk, pParams );
    if ( fOracle )
        pCutOracle = Cut_OracleStart( pCutMan );
    Cut_ManStop( pCutMan );
    if ( fOracle )
    {
        Abc_NtkCutsOracle( pNtk, pCutOracle );
        Cut_OracleStop( pCutOracle );
    }
    return 0;

usage:
    fprintf( pErr, "usage: cut [-K num] [-M num] [-tfdxyzmvh]\n" );
    fprintf( pErr, "\t         computes k-feasible cuts for the AIG\n" );
    fprintf( pErr, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    fprintf( pErr, "\t-M num : max number of cuts stored at a node [default = %d]\n",      pParams->nKeepMax );
    fprintf( pErr, "\t-t     : toggle truth table computation [default = %s]\n",           pParams->fTruth?   "yes": "no" );
    fprintf( pErr, "\t-f     : toggle filtering of duplicated/dominated [default = %s]\n", pParams->fFilter?  "yes": "no" );
    fprintf( pErr, "\t-d     : toggle dropping when fanouts are done [default = %s]\n",    pParams->fDrop?    "yes": "no" );
    fprintf( pErr, "\t-x     : toggle computing only DAG cuts [default = %s]\n",           pParams->fDag?     "yes": "no" );
    fprintf( pErr, "\t-y     : toggle computing only tree cuts [default = %s]\n",          pParams->fTree?    "yes": "no" );
    fprintf( pErr, "\t-g     : toggle computing only global cuts [default = %s]\n",        pParams->fGlobal?  "yes": "no" );
    fprintf( pErr, "\t-l     : toggle computing only local cuts [default = %s]\n",         pParams->fLocal?   "yes": "no" );
    fprintf( pErr, "\t-z     : toggle fancy computations [default = %s]\n",                pParams->fFancy?   "yes": "no" );
    fprintf( pErr, "\t-m     : toggle delay-oriented FPGA mapping [default = %s]\n",       pParams->fMap?     "yes": "no" );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n",      pParams->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern Cut_Man_t * Abc_NtkSeqCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-M\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
/*
    if ( !Abc_NtkIsSeq(pNtk) )
    {
        fprintf( pErr, "Sequential cuts can be computed for sequential AIGs (run \"seq\").\n" );
        return 1;
    }
*/
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        fprintf( pErr, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }

    pCutMan = Abc_NtkSeqCuts( pNtk, pParams );
    Cut_ManStop( pCutMan );
    return 0;

usage:
    fprintf( pErr, "usage: scut [-K num] [-M num] [-tvh]\n" );
    fprintf( pErr, "\t         computes k-feasible cuts for the sequential AIG\n" );
    fprintf( pErr, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    fprintf( pErr, "\t-M num : max number of cuts stored at a node [default = %d]\n",      pParams->nKeepMax );
    fprintf( pErr, "\t-t     : toggle truth table computation [default = %s]\n",           pParams->fTruth?   "yes": "no" );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n",      pParams->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose;
    extern void Abc_NtkEspresso( Abc_Ntk_t * pNtk, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "SOP minimization is possible for logic networks (run \"renode\").\n" );
        return 1;
    }
    Abc_NtkEspresso( pNtk, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: espresso [-vh]\n" );
    fprintf( pErr, "\t         minimizes SOPs of the local functions using Espresso\n" );
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
int Abc_CommandGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nVars;
    int fAdder;
    int fSorter;
    int fVerbose;
    char * FileName;
    extern void Abc_GenAdder( char * pFileName, int nVars );
    extern void Abc_GenSorter( char * pFileName, int nVars );


    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nVars = 8;
    fAdder = 0;
    fSorter = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nasvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 ) 
                goto usage;
            break;
        case 'a':
            fAdder ^= 1;
            break;
        case 's':
            fSorter ^= 1;
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
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( fAdder )
        Abc_GenAdder( FileName, nVars );
    else if ( fSorter )
        Abc_GenSorter( FileName, nVars );
    else
        printf( "Type of circuit is not specified.\n" );
    return 0;

usage:
    fprintf( pErr, "usage: gen [-N] [-asvh] <file>\n" );
    fprintf( pErr, "\t         generates simple circuits\n" );
    fprintf( pErr, "\t-N num : the number of variables [default = %d]\n", nVars );  
    fprintf( pErr, "\t-a     : toggle ripple-carry adder [default = %s]\n", fAdder? "yes": "no" );  
    fprintf( pErr, "\t-s     : toggle simple sorter [default = %s]\n", fSorter? "yes": "no" );  
    fprintf( pErr, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t<file> : output file name\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandXyz( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;//, * pNtkTemp;
    int c;
    int nLutMax;
    int nPlaMax;
    int RankCost;
    int fFastMode;
    int fRewriting;
    int fSynthesis;
    int fVerbose;
//    extern Abc_Ntk_t * Abc_NtkXyz( Abc_Ntk_t * pNtk, int nPlaMax, bool fEsop, bool fSop, bool fInvs, bool fVerbose );
    extern void * Abc_NtkPlayer( void * pNtk, int nLutMax, int nPlaMax, int RankCost, int fFastMode, int fRewriting, int fSynthesis, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nLutMax    = 8;
    nPlaMax    = 128;
    RankCost   = 96000;
    fFastMode  = 1;
    fRewriting = 0;
    fSynthesis = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LPRfrsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutMax < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPlaMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPlaMax < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            RankCost = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( RankCost < 0 ) 
                goto usage;
            break;
        case 'f':
            fFastMode ^= 1;
            break;
        case 'r':
            fRewriting ^= 1;
            break;
        case 's':
            fSynthesis ^= 1;
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
        fprintf( pErr, "Only works for strashed networks.\n" );
        return 1;
    }
/*
    if ( nLutMax < 2 || nLutMax > 12 || nPlaMax < 8 || nPlaMax > 128  )
    {
        fprintf( pErr, "Incorrect LUT/PLA parameters.\n" );
        return 1;
    }
*/
    // run the command
//    pNtkRes = Abc_NtkXyz( pNtk, nPlaMax, 1, 0, fInvs, fVerbose );
/*
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 1 );
        pNtkRes = Abc_NtkPlayer( pNtkTemp, nLutMax, nPlaMax, RankCost, fFastMode, fRewriting, fSynthesis, fVerbose );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes = Abc_NtkPlayer( pNtk, nLutMax, nPlaMax, RankCost, fFastMode, fRewriting, fSynthesis, fVerbose );
*/
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: xyz [-L num] [-P num] [-R num] [-frsvh]\n" );
    fprintf( pErr, "\t         specilized LUT/PLA decomposition\n" );
    fprintf( pErr, "\t-L num : maximum number of LUT inputs (2<=num<=8) [default = %d]\n", nLutMax );
    fprintf( pErr, "\t-P num : maximum number of PLA inputs/cubes (8<=num<=128) [default = %d]\n", nPlaMax );
    fprintf( pErr, "\t-R num : maximum are of one decomposition rank [default = %d]\n", RankCost );
    fprintf( pErr, "\t-f     : toggle using fast LUT mapping mode [default = %s]\n", fFastMode? "yes": "no" );
    fprintf( pErr, "\t-r     : toggle using one pass of AIG rewriting [default = %s]\n", fRewriting? "yes": "no" );
    fprintf( pErr, "\t-s     : toggle using synthesis by AIG rewriting [default = %s]\n", fSynthesis? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDouble( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFrames;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDouble( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames    = 50;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
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

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        fprintf( pErr, "Only works for logic SOP networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDouble( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: double [-vh]\n" );
    fprintf( pErr, "\t         puts together two parallel copies of the current network\n" );
//    fprintf( pErr, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
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
    Abc_Ntk_t * pNtk;//, * pNtkRes;
    int c;
    int nLevels;
//    extern Abc_Ntk_t * Abc_NtkNewAig( Abc_Ntk_t * pNtk );
//    extern Abc_Ntk_t * Abc_NtkIvy( Abc_Ntk_t * pNtk );
    extern void Abc_NtkMaxFlowTest( Abc_Ntk_t * pNtk );
    extern int Pr_ManProofTest( char * pFileName );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nLevels = 128;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
/*
    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsSeq(pNtk) )
    {
        fprintf( pErr, "Only works for non-sequential networks.\n" );
        return 1;
    }
*/

//    Abc_NtkTestEsop( pNtk );
//    Abc_NtkTestSop( pNtk );
//    printf( "This command is currently not used.\n" );
    // run the command
//    pNtkRes = Abc_NtkMiterForCofactors( pNtk, 0, 0, -1 );
//    pNtkRes = Abc_NtkNewAig( pNtk );

/*
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
*/

//    if ( Cut_CellIsRunning() )
//        Cut_CellDumpToFile();
//    else
//        Cut_CellPrecompute();
//        Cut_CellLoad();
/*
        {
            Abc_Ntk_t * pNtkRes;
            extern Abc_Ntk_t * Abc_NtkTopmost( Abc_Ntk_t * pNtk, int nLevels );
            pNtkRes = Abc_NtkTopmost( pNtk, nLevels );
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        }
*/
//    Abc_NtkSimulteBuggyMiter( pNtk );

//    Rwr_Temp();
//    Abc_MvExperiment();
//    Ivy_TruthTest();


//    Ivy_TruthEstimateNodesTest();
/*
    pNtkRes = Abc_NtkIvy( pNtk );
//    pNtkRes = Abc_NtkPlayer( pNtk, nLevels, 0 );
//    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
*/
//    Abc_NtkMaxFlowTest( pNtk );
    Pr_ManProofTest( "trace.cnf" );
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
int Abc_CommandIStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    extern Abc_Ntk_t * Abc_NtkIvyStrash( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 1 );
        pNtkRes = Abc_NtkIvyStrash( pNtkTemp );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes = Abc_NtkIvyStrash( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: istrash [-h]\n" );
    fprintf( pErr, "\t         perform sequential structural hashing\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c, nInputs;
    extern void Abc_NtkIvyCuts( Abc_Ntk_t * pNtk, int nInputs );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-K\" should be followed by an integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    Abc_NtkIvyCuts( pNtk, nInputs );
    return 0;

usage:
    fprintf( pErr, "usage: icut [-K num] [-h]\n" );
    fprintf( pErr, "\t         computes sequential cuts of the given size\n" );
    fprintf( pErr, "\t-K num : the number of cut inputs (2 <= num <= 6) [default = %d]\n", nInputs );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewrite( Abc_Ntk_t * pNtk, int fUpdateLevel, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyRewrite( pNtk, fUpdateLevel, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: irw [-lzvh]\n" );
    fprintf( pErr, "\t         perform combinational AIG rewriting\n" );
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
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
int Abc_CommandIRewriteSeq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewriteSeq( Abc_Ntk_t * pNtk, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyRewriteSeq( pNtk, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: irws [-zvh]\n" );
    fprintf( pErr, "\t         perform sequential AIG rewriting\n" );
//    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    fprintf( pErr, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
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
int Abc_CommandIResyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyResyn( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyResyn( pNtk, fUpdateLevel, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: iresyn [-lvh]\n" );
    fprintf( pErr, "\t         performs combinational resynthesis\n" );
    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandISat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    int nConfLimit;

    extern Abc_Ntk_t * Abc_NtkIvySat( Abc_Ntk_t * pNtk, int nConfLimit, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nConfLimit   = 100000;   
    fUpdateLevel = 1;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Clzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvySat( pNtk, nConfLimit, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: isat [-C num] [-vh]\n" );
    fprintf( pErr, "\t         tries to prove the miter constant 0\n" );
    fprintf( pErr, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
//    fprintf( pErr, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandIFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fProve, fVerbose, fDoSparse;
    int nConfLimit;

    extern Abc_Ntk_t * Abc_NtkIvyFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nConfLimit   = 100;   
    fDoSparse    = 0;
    fProve       = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
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

    pNtkRes = Abc_NtkIvyFraig( pNtk, nConfLimit, fDoSparse, fProve, 0, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: ifraig [-C num] [-spvh]\n" );
    fprintf( pErr, "\t         performs fraiging using a new method\n" );
    fprintf( pErr, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfLimit );
    fprintf( pErr, "\t-s     : toggle considering sparse functions [default = %s]\n", fDoSparse? "yes": "no" );
    fprintf( pErr, "\t-p     : toggle proving the miter outputs [default = %s]\n", fProve? "yes": "no" );
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
int Abc_CommandIProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Prove_Params_t Params, * pParams = &Params;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    int c, clk, RetValue;

    extern int Abc_NtkIvyProve( Abc_Ntk_t ** ppNtk, void * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Prove_ParamsSetDefault( pParams );
    pParams->fUseRewriting = 1;
    pParams->fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            pParams->fUseRewriting ^= 1;
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

    clk = clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0 );

    RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        if ( pSimInfo[0] != 1 )
            printf( "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        free( pSimInfo );
    }
 
    if ( RetValue == -1 ) 
        printf( "UNDECIDED      " );
    else if ( RetValue == 0 )
        printf( "SATISFIABLE    " );
    else
        printf( "UNSATISFIABLE  " );
    //printf( "\n" );

    PRT( "Time", clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    return 0;

usage:
    fprintf( pErr, "usage: iprove [-rvh]\n" );
    fprintf( pErr, "\t         performs CEC using a new method\n" );
    fprintf( pErr, "\t-r     : toggle AIG rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose printout [default = %s]\n", pParams->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandHaig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUseZeroCost, fVerbose, nIters;
    extern Abc_Ntk_t * Abc_NtkIvyHaig( Abc_Ntk_t * pNtk, int nIters, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nIters       = 2;
    fUseZeroCost = 0;
    fVerbose     = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Izvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 ) 
                goto usage;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyHaig( pNtk, nIters, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: haig [-Izvh]\n" );
    fprintf( pErr, "\t         prints HAIG stats after sequential rewriting\n" );
    fprintf( pErr, "\t-I num : the number of rewriting iterations [default = %d]\n", nIters );
    fprintf( pErr, "\t-z     : toggle zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
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
int Abc_CommandMini( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkMiniBalance( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Only works for combinatinally strashed AIG networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkMiniBalance( pNtk );
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: mini [-h]\n" );
    fprintf( pErr, "\t         perform balancing using new package\n" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nFrames;
    int fInit;
    int fVerbose;

    extern void Abc_NtkBmc( Abc_Ntk_t * pNtk, int nFrames, int fInit, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames  = 5;
    fInit    = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'i':
            fInit ^= 1;
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
        Abc_NtkBmc( pNtk, nFrames, fInit, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 1 );
        Abc_NtkBmc( pNtk, nFrames, fInit, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    fprintf( pErr, "usage: bmc [-K num] [-ivh]\n" );
    fprintf( pErr, "\t         perform bounded model checking\n" );
    fprintf( pErr, "\t-K num : number of time frames [default = %d]\n", nFrames );
    fprintf( pErr, "\t-i     : toggle initialization of the first frame [default = %s]\n", fInit? "yes": "no" );
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
int Abc_CommandFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Fraig_Params_t Params, * pParams = &Params;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fAllNodes;
    int fExdc;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
    pParams->fDoSparse  =    0; // performs equiv tests for sparse functions 
    pParams->fChoicing  =    0; // enables recording structural choices
    pParams->fTryProve  =    0; // tries to solve the final miter
    pParams->fVerbose   =    0; // the verbosiness flag
    pParams->fVerboseP  =    0; // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "RDCrscpvaeh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-R\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-D\" should be followed by an integer.\n" );
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
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
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
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes );
        pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
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
    fprintf( pErr, "usage: fraig [-R num] [-D num] [-C num] [-rscpvah]\n" );
    fprintf( pErr, "\t         transforms a logic network into a functionally reduced AIG\n" );
    fprintf( pErr, "\t-R num : number of random patterns (127 < num < 32769) [default = %d]\n",     pParams->nPatsRand );
    fprintf( pErr, "\t-D num : number of systematic patterns (127 < num < 32769) [default = %d]\n", pParams->nPatsDyna );
    fprintf( pErr, "\t-C num : number of backtracks for one SAT problem [default = %s]\n",    pParams->nBTLimit==-1? "infinity" : Buffer );
    fprintf( pErr, "\t-r     : toggle functional reduction [default = %s]\n",                 pParams->fFuncRed? "yes": "no" );
    fprintf( pErr, "\t-s     : toggle considering sparse functions [default = %s]\n",         pParams->fDoSparse? "yes": "no" );
    fprintf( pErr, "\t-c     : toggle accumulation of choices [default = %s]\n",              pParams->fChoicing? "yes": "no" );
    fprintf( pErr, "\t-p     : toggle proving the miter outputs [default = %s]\n",              pParams->fTryProve? "yes": "no" );
    fprintf( pErr, "\t-v     : toggle verbose output [default = %s]\n",                       pParams->fVerbose?  "yes": "no" );
    fprintf( pErr, "\t-e     : toggle functional sweeping using EXDC [default = %s]\n",       fExdc? "yes": "no" );
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
    int fExdc;
    int fVerbose;
    extern bool Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fUseInv   = 1;
    fExdc     = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ievh" ) ) != EOF )
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
    if ( !Abc_NtkFraigSweep( pNtk, fUseInv, fExdc, fVerbose ) )
    {
        fprintf( pErr, "Sweeping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pErr, "usage: fraig_sweep [-evh]\n" );
    fprintf( pErr, "\t        performs technology-dependent sweep\n" );
    fprintf( pErr, "\t-e    : toggle functional sweeping using EXDC [default = %s]\n", fExdc? "yes": "no" );
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
int Abc_CommandFraigDress( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    char * pFileName;
    int c;
    int fVerbose;
    extern void Abc_NtkDress( Abc_Ntk_t * pNtk, char * pFileName, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose = 1;
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command works only for logic networks.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind && argc != globalUtilOptind + 1 )
        goto usage;
    if ( argc == globalUtilOptind && Abc_NtkSpec(pNtk) == NULL )
    {
        fprintf( pErr, "The current network has no spec.\n" );
        return 1;
    }
    // get the input file name
    pFileName = (argc == globalUtilOptind + 1) ? argv[globalUtilOptind] : Abc_NtkSpec(pNtk);
    // modify the current network
    Abc_NtkDress( pNtk, pFileName, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: dress [-vh] <file>\n" );
    fprintf( pErr, "\t         transfers internal node names from file to the current network\n" );
    fprintf( pErr, "\t<file> : network with names (if not given, the current network spec is used)\n" );  
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
    extern bool Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    DelayTarget =-1;
    fRecovery   = 1;
    fSweep      = 1;
    fSwitching  = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Daspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
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
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
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
        Abc_NtkFraigSweep( pNtkRes, 0, 0, 0 );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "not used" );
    else
        sprintf( Buffer, "%.3f", DelayTarget );
    fprintf( pErr, "usage: map [-D float] [-aspvh]\n" );
    fprintf( pErr, "\t           performs standard cell mapping of the current network\n" );
    fprintf( pErr, "\t-D float : sets the global required times [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    fprintf( pErr, "\t-s       : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    fprintf( pErr, "\t-p       : optimizes power by minimizing switching [default = %s]\n", fSwitching? "yes": "no" );
    fprintf( pErr, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h       : print the command usage\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(pNtk) )
    {
        fprintf( pErr, "Cannot unmap the network that is not mapped.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkMapToSop( pNtk ) )
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
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
int Abc_CommandSuperChoiceLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nLutSize;
    int nCutSizeMax;
    int fVerbose;
    extern int Abc_NtkSuperChoiceLut( Abc_Ntk_t * pNtk, int nLutSize, int nCutSizeMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-K\" should be followed by a positive integer.\n" );
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
                fprintf( pErr, "Command line switch \"-N\" should be followed by a positive integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // convert the network into the SOP network
    pNtkRes = Abc_NtkAigToLogicSop( pNtk );

    // get the new network
    if ( !Abc_NtkSuperChoiceLut( pNtkRes, nLutSize, nCutSizeMax, fVerbose ) )
    {
        Abc_NtkDelete( pNtkRes );
        fprintf( pErr, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: scl [-K num] [-N num] [-vh]\n" );
    fprintf( pErr, "\t        performs superchoicing for K-LUTs\n" );
    fprintf( pErr, "\t        (accumulate: \"r file.blif; b; scl; f -ac; wb file_sc.blif\")\n" );
    fprintf( pErr, "\t        (FPGA map: \"r file_sc.blif; ft; read_lut lutlibK; fpga\")\n" );
    fprintf( pErr, "\t-K num : the number of LUT inputs [default = %d]\n", nLutSize );
    fprintf( pErr, "\t-N num : the max size of the cut [default = %d]\n", nCutSizeMax );
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
int Abc_CommandFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    char LutSize[100];
    FILE * pOut, * pErr;
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
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-D\" should be followed by a floating point number.\n" );
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
                fprintf( pErr, "Command line switch \"-K\" should be followed by a positive integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    // create the new LUT library
    if ( nLutSize >= 3 && nLutSize <= 10 )
        Fpga_SetSimpleLutLib( nLutSize );
/*
    else
    {
        fprintf( pErr, "Cannot perform FPGA mapping with LUT size %d.\n", nLutSize );
        return 1;
    }
*/
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        fprintf( pOut, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
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
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
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
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "best possible" );
    else
        sprintf( Buffer, "%.2f", DelayTarget );
    if ( nLutSize == -1 ) 
        sprintf( LutSize, "library" );
    else
        sprintf( LutSize, "%d", nLutSize );
    fprintf( pErr, "usage: fpga [-D float] [-K num] [-aplvh]\n" );
    fprintf( pErr, "\t           performs FPGA mapping of the current network\n" );
    fprintf( pErr, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    fprintf( pErr, "\t-p       : optimizes power by minimizing switching activity [default = %s]\n", fSwitching? "yes": "no" );
    fprintf( pErr, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", fLatchPaths? "yes": "no" );
    fprintf( pErr, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-K num   : the number of LUT inputs (2 < num < 11) [default = %s]%s\n", LutSize, (nLutSize == -1 ? " (type \"print_lut\")" : "") );
    fprintf( pErr, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpgaFast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fVerbose;
    int nLutSize;
    float DelayTarget;

    extern Abc_Ntk_t * Abc_NtkFpgaFast( Abc_Ntk_t * pNtk, int nLutSize, int fRecovery, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-D\" should be followed by a floating point number.\n" );
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
                fprintf( pErr, "Command line switch \"-K\" should be followed by a positive integer.\n" );
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
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        fprintf( pOut, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
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
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
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
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "not used" );
    else
        sprintf( Buffer, "%.2f", DelayTarget );
    fprintf( pErr, "usage: ffpga [-K num] [-avh]\n" );
    fprintf( pErr, "\t           performs fast FPGA mapping of the current network\n" );
    fprintf( pErr, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
//    fprintf( pErr, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-K num   : the number of LUT inputs (2 < num < 32) [default = %d]\n", nLutSize );
    fprintf( pErr, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    char LutSize[100];
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    If_Par_t Pars, * pPars = &Pars;
    int c;
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  4;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  1;
    pPars->fLatchPaths =  0;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  0;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->nLatches    =  pNtk? Abc_NtkLatchNum(pNtk) : 0;
    pPars->fLiftLeaves =  0;
    pPars->pLutLib     =  Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  NULL;   

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFADpaflrstvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-K\" should be followed by a positive integer.\n" );
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
                fprintf( pErr, "Command line switch \"-C\" should be followed by a positive integer.\n" );
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
                fprintf( pErr, "Command line switch \"-F\" should be followed by a positive integer.\n" );
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
                fprintf( pErr, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaIters < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'p':
            pPars->fPreprocess ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'f':
            pPars->fFancy ^= 1;
            break;
        case 'l':
            pPars->fLatchPaths ^= 1;
            break;
        case 'r':
            pPars->fExpRed ^= 1;
            break;
        case 's':
            pPars->fSeqMap ^= 1;
            break;
        case 't':
            pPars->fLiftLeaves ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
/*
    if ( pPars->fSeq )
    {
        fprintf( pErr, "Sequential mapping is currently being implemented.\n" );
        return 1;
    }
*/
    if ( pPars->fSeqMap && pPars->nLatches == 0 )
    {
        fprintf( pErr, "The network has no latches. Use combinational mapping instead of sequential.\n" );
        return 1;
    }

    if ( pPars->nLutSize < 3 || pPars->nLutSize > IF_MAX_LUTSIZE )
    {
        fprintf( pErr, "Incorrect LUT size (%d).\n", pPars->nLutSize );
        return 1;
    }

    if ( pPars->nCutsMax < 2 || pPars->nCutsMax >= (1<<12) )
    {
        fprintf( pErr, "Incorrect number of cuts.\n" );
        return 1;
    }

    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        printf( "Performing FPGA mapping with choices.\n" );
//        printf( "Currently mapping with choices is not enabled.\n" );
        pPars->fTruth = 1;
//        return 1;
    }

    if ( pPars->fTruth && pPars->nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        fprintf( pErr, "Mapping with choices requires computing truth tables. In this case, the LUT size cannot be more than %d.\n", IF_MAX_FUNC_LUTSIZE );
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
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        fprintf( pOut, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkIf( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            fprintf( pErr, "FPGA mapping has failed.\n" );
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
            fprintf( pErr, "FPGA mapping has failed.\n" );
            return 0;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 ) 
        sprintf( Buffer, "best possible" );
    else
        sprintf( Buffer, "%.2f", pPars->DelayTarget );
    if ( pPars->nLutSize == -1 ) 
        sprintf( LutSize, "library" );
    else
        sprintf( LutSize, "%d", pPars->nLutSize );
    fprintf( pErr, "usage: if [-K num] [-C num] [-F num] [-A num] [-D float] [-pafrsvh]\n" );
    fprintf( pErr, "\t           performs FPGA technology mapping of the network\n" );
    fprintf( pErr, "\t-K num   : the number of LUT inputs (2 < num < %d) [default = %s]\n", IF_MAX_LUTSIZE+1, LutSize );
    fprintf( pErr, "\t-C num   : the max number of cuts to use (1 < num < 2^12) [default = %d]\n", pPars->nCutsMax );
    fprintf( pErr, "\t-F num   : the number of area flow recovery iterations (num >= 0) [default = %d]\n", pPars->nFlowIters );
    fprintf( pErr, "\t-A num   : the number of exact area recovery iterations (num >= 0) [default = %d]\n", pPars->nAreaIters );
    fprintf( pErr, "\t-D float : sets the delay constraint for the mapping [default = %s]\n", Buffer );  
    fprintf( pErr, "\t-p       : toggles preprocessing using several starting points [default = %s]\n", pPars->fPreprocess? "yes": "no" );
    fprintf( pErr, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fArea? "yes": "no" );
//    fprintf( pErr, "\t-f       : toggles one fancy feature [default = %s]\n", pPars->fFancy? "yes": "no" );
    fprintf( pErr, "\t-r       : enables expansion/reduction of the best cuts [default = %s]\n", pPars->fExpRed? "yes": "no" );
    fprintf( pErr, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", pPars->fLatchPaths? "yes": "no" );
    fprintf( pErr, "\t-s       : toggles sequential mapping [default = %s]\n", pPars->fSeqMap? "yes": "no" );
//    fprintf( pErr, "\t-t       : toggles the use of true sequential cuts [default = %s]\n", pPars->fLiftLeaves? "yes": "no" );
    fprintf( pErr, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h       : prints the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    int c, i;
    int fZeros;
    int fOnes;
    int fRandom;
    int fDontCare;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fZeros    = 0;
    fOnes     = 0;
    fRandom   = 0;
    fDontCare = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "zordh" ) ) != EOF )
    {
        switch ( c )
        {
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
        fprintf( pErr, "The current network is combinational.\n" );
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
    else
        printf( "The initial states remain unchanged.\n" );
    return 0;

usage:
    fprintf( pErr, "usage: init [-zordh]\n" );
    fprintf( pErr, "\t        resets initial states of all latches\n" );
    fprintf( pErr, "\t-z    : set zeros initial states [default = %s]\n", fZeros? "yes": "no" );
    fprintf( pErr, "\t-o    : set ones initial states [default = %s]\n", fOnes? "yes": "no" );
    fprintf( pErr, "\t-d    : set don't-care initial states [default = %s]\n", fDontCare? "yes": "no" );
    fprintf( pErr, "\t-r    : set random initial states [default = %s]\n", fRandom? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nLatches;
    extern void Abc_NtkLatchPipe( Abc_Ntk_t * pNtk, int nLatches );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-L\" should be followed by a positive integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        fprintf( pErr, "The current network is combinational.\n" );
        return 1;
    }

    // update the network
    Abc_NtkLatchPipe( pNtk, nLatches );
    return 0;

usage:
    fprintf( pErr, "usage: pipe [-L num] [-h]\n" );
    fprintf( pErr, "\t         inserts the given number of latches at each PI for pipelining\n" );
    fprintf( pErr, "\t-L num : the number of latches to insert [default = %d]\n", nLatches );
    fprintf( pErr, "\t-h     : print the command usage\n");
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

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        fprintf( pErr, "The network has no latches.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Conversion to sequential AIG works only for combinational AIGs (run \"strash\").\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkAigToSeq( pNtk );
    pNtkRes = NULL;
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
    fprintf( pErr, "\t        converts AIG into sequential AIG\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
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
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fShare;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
/*
    if ( !Abc_NtkIsSeq(pNtk) )
    {
        fprintf( pErr, "Conversion to combinational AIG works only for sequential AIG (run \"seq\").\n" );
        return 1;
    }
*/
    // share the latches on the fanout edges
//    if ( fShare )
//        Seq_NtkShareFanouts(pNtk);

    // get the new network
//    pNtkRes = Abc_NtkSeqToLogicSop( pNtk );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Converting sequential AIG into an SOP logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: unseq [-sh]\n" );
    fprintf( pErr, "\t        converts sequential AIG into an SOP logic network\n" );
    fprintf( pErr, "\t-s    : toggle sharing latches [default = %s]\n", fShare? "yes": "no" );
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
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMaxIters;
    int fForward;
    int fBackward;
    int fVerbose;
    int Mode;
    extern int Abc_NtkRetime( Abc_Ntk_t * pNtk, int Mode, int fForwardOnly, int fBackwardOnly, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Mode      =  5;
    fForward  =  0;
    fBackward =  0;
    fVerbose  =  0;
    nMaxIters = 15;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Mode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Mode < 0 ) 
                goto usage;
            break;
        case 'f':
            fForward ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
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

    if ( fForward && fBackward )
    {
        fprintf( pErr, "Only one switch \"-f\" or \"-b\" can be selected at a time.\n" );
        return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
        fprintf( pErr, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( Mode < 0 || Mode > 6 )
    {
        fprintf( pErr, "The mode (%d) is incorrect. Retiming is not performed.\n", Mode );
        return 0;
    }

    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            fprintf( pErr, "Retiming with choice nodes is not implemented.\n" );
            return 0;
        }
        // convert the network into an SOP network
        pNtkRes = Abc_NtkAigToLogicSop( pNtk );
        // perform the retiming
        Abc_NtkRetime( pNtkRes, Mode, fForward, fBackward, fVerbose );
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }

    // get the network in the SOP form
    if ( !Abc_NtkLogicToSop(pNtk, 0) )
    {
        printf( "Converting to SOPs has failed.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "The network is not a logic network. Retiming is not performed.\n" );
        return 0;
    }

    // perform the retiming
    Abc_NtkRetime( pNtk, Mode, fForward, fBackward, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: retime [-M num] [-fbvh]\n" );
    fprintf( pErr, "\t         retimes the current network using one of the algorithms:\n" );
    fprintf( pErr, "\t             1: most forward retiming\n" );
    fprintf( pErr, "\t             2: most backward retiming\n" );
    fprintf( pErr, "\t             3: forward and backward min-area retiming\n" );
    fprintf( pErr, "\t             4: forward and backward min-delay retiming\n" );
    fprintf( pErr, "\t             5: mode 3 followed by mode 4\n" );
    fprintf( pErr, "\t             6: Pan's optimum-delay retiming using binary search\n" );
    fprintf( pErr, "\t-M num : the retiming algorithm to use [default = %d]\n", Mode );
    fprintf( pErr, "\t-f     : enables forward-only retiming in modes 3,4,5 [default = %s]\n", fForward? "yes": "no" );
    fprintf( pErr, "\t-b     : enables backward-only retiming in modes 3,4,5 [default = %s]\n", fBackward? "yes": "no" );
    fprintf( pErr, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
//    fprintf( pErr, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
//    fprintf( pErr, "\t-f     : toggle forward retiming (for AIGs) [default = %s]\n", fForward? "yes": "no" );
//    fprintf( pErr, "\t-b     : toggle backward retiming (for AIGs) [default = %s]\n", fBackward? "yes": "no" );
//    fprintf( pErr, "\t-i     : toggle computation of initial state [default = %s]\n", fInitial? "yes": "no" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    int c, nMaxIters;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-I\" should be followed by a positive integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkHasAig(pNtk) )
    {
/*
        // quit if there are choice nodes
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            fprintf( pErr, "Currently cannot map/retime networks with choice nodes.\n" );
            return 0;
        }
*/
//        if ( Abc_NtkIsStrash(pNtk) )
//            pNtkNew = Abc_NtkAigToSeq(pNtk);
//        else
//            pNtkNew = Abc_NtkDup(pNtk);
        pNtkNew = NULL;
    }
    else
    {
        // strash and balance the network
        pNtkNew = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Strashing before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Converting into a seq AIG before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        fprintf( pOut, "The network was strashed and balanced before FPGA mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_NtkFpgaMapRetime( pNtkNew, nMaxIters, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
//        fprintf( pErr, "Sequential FPGA mapping has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return 0;
    }
    Abc_NtkDelete( pNtkNew );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: sfpga [-I num] [-vh]\n" );
    fprintf( pErr, "\t         performs integrated sequential FPGA mapping/retiming\n" );
    fprintf( pErr, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
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
int Abc_CommandSeqMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    int c, nMaxIters;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
                fprintf( pErr, "Command line switch \"-I\" should be followed by a positive integer.\n" );
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkHasAig(pNtk) )
    {
/*
        // quit if there are choice nodes
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            fprintf( pErr, "Currently cannot map/retime networks with choice nodes.\n" );
            return 0;
        }
*/
//        if ( Abc_NtkIsStrash(pNtk) )
//            pNtkNew = Abc_NtkAigToSeq(pNtk);
//        else
//            pNtkNew = Abc_NtkDup(pNtk);
        pNtkNew = NULL;
    }
    else
    {
        // strash and balance the network
        pNtkNew = Abc_NtkStrash( pNtk, 0, 0 );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Strashing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Balancing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            fprintf( pErr, "Converting into a seq AIG before SC mapping/retiming has failed.\n" );
            return 1;
        }

        fprintf( pOut, "The network was strashed and balanced before SC mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_MapRetime( pNtkNew, nMaxIters, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
//        fprintf( pErr, "Sequential FPGA mapping has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return 0;
    }
    Abc_NtkDelete( pNtkNew );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: smap [-I num] [-vh]\n" );
    fprintf( pErr, "\t         performs integrated sequential standard-cell mapping/retiming\n" );
    fprintf( pErr, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
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
    int nFrames;
    int fExdc;
    int fImp;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkVanEijk( Abc_Ntk_t * pNtk, int nFrames, int fExdc, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkVanImp( Abc_Ntk_t * pNtk, int nFrames, int fExdc, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    printf( "This command is not implemented\n" );

    // set defaults
    nFrames  = 1;
    fExdc    = 1;
    fImp     = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Feivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames <= 0 ) 
                goto usage;
            break;
        case 'e':
            fExdc ^= 1;
            break;
        case 'i':
            fImp ^= 1;
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
        fprintf( pErr, "Sequential sweep works only for structurally hashed networks (run \"strash\").\n" );
        return 1;
    }

    // get the new network
//    if ( fImp )
//        pNtkRes = Abc_NtkVanImp( pNtk, nFrames, fExdc, fVerbose );
//    else
//        pNtkRes = Abc_NtkVanEijk( pNtk, nFrames, fExdc, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        fprintf( pErr, "Sequential FPGA mapping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pErr, "usage: ssweep [-F num] [-eivh]\n" );
    fprintf( pErr, "\t         performs sequential sweep using van Eijk's method\n" );
    fprintf( pErr, "\t-F num : number of time frames in the base case [default = %d]\n", nFrames );
    fprintf( pErr, "\t-e     : toggle writing EXDC network [default = %s]\n", fExdc? "yes": "no" );
    fprintf( pErr, "\t-i     : toggle computing implications [default = %s]\n", fImp? "yes": "no" );
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
int Abc_CommandSeqCleanup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int fLatchSweep;
    int fAutoSweep;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fLatchSweep = 0;
    fAutoSweep  = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lavh" ) ) != EOF )
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
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "Only works for logic networks.\n" );
        return 1;
    }
    // modify the current network
    Abc_NtkCleanupSeq( pNtk, fLatchSweep, fAutoSweep, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: scleanup [-lavh]\n" );
    fprintf( pErr, "\t         performs sequential cleanup\n" );
    fprintf( pErr, "\t         - removes nodes/latches that do not feed into POs\n" );
    fprintf( pErr, "\t         - removes and shared latches driven by constants\n" );
    fprintf( pErr, "\t         - replaces autonomous logic by free PI variables\n" );
    fprintf( pErr, "\t           (the latter may change sequential behaviour)\n" );
    fprintf( pErr, "\t-l     : toggle sweeping latches [default = %s]\n", fLatchSweep? "yes": "no" );
    fprintf( pErr, "\t-a     : toggle removing autonomous logic [default = %s]\n", fAutoSweep? "yes": "no" );
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
int Abc_CommandCycle( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nFrames;
    int fVerbose;
    extern void Abc_NtkCycleInitState( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );
    extern void Abc_NtkCycleInitStateSop( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames    = 100;
    fVerbose   =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
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

    if ( !Abc_NtkIsStrash(pNtk) && !Abc_NtkIsSopLogic(pNtk) )
    {
        fprintf( pErr, "Only works for strashed networks or logic SOP networks.\n" );
        return 1;
    }

    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkCycleInitState( pNtk, nFrames, fVerbose );
    else
        Abc_NtkCycleInitStateSop( pNtk, nFrames, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: cycle [-F num] [-vh]\n" );
    fprintf( pErr, "\t         cycles sequiential circuit for the given number of timeframes\n" );
    fprintf( pErr, "\t         to derive a new initial state (which may be on the envelope)\n" );
    fprintf( pErr, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandXsim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int nFrames;
    int fInputs;
    int fVerbose;
    extern void Abc_NtkXValueSimulate( Abc_Ntk_t * pNtk, int nFrames, int fInputs, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    nFrames    = 10;
    fInputs    =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'i':
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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "Only works for strashed networks.\n" );
        return 1;
    }

    Abc_NtkXValueSimulate( pNtk, nFrames, fInputs, fVerbose );
    return 0;

usage:
    fprintf( pErr, "usage: xsim [-F num] [-ivh]\n" );
    fprintf( pErr, "\t         performs X-valued simulation of the AIG\n" );
    fprintf( pErr, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    fprintf( pErr, "\t-i     : toggle X-valued state or X-valued inputs [default = %s]\n", fInputs? "inputs": "state" );
    fprintf( pErr, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
    int nSeconds;
    int nConfLimit;
    int nInsLimit;

    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );
    extern void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );


    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nConfLimit = 10000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
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

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // perform equivalence checking
    if ( fSat )
        Abc_NtkCecSat( pNtk1, pNtk2, nConfLimit, nInsLimit );
    else
        Abc_NtkCecFraig( pNtk1, pNtk2, nSeconds, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: cec [-T num] [-C num] [-I num] [-svh] <file1> <file2>\n" );
    fprintf( pErr, "\t         performs combinational equivalence checking\n" );
    fprintf( pErr, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    fprintf( pErr, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    fprintf( pErr, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    fprintf( pErr, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    fprintf( pErr, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
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
int Abc_CommandSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;
    int nFrames;
    int nSeconds;
    int nConfLimit;
    int nInsLimit;

    extern void Abc_NtkSecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit, int nFrames );
    extern int Abc_NtkSecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nFrames, int fVerbose );


    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nFrames  =  5;
    nSeconds = 20;
    nConfLimit = 10000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTCIsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames <= 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        printf( "The network has no latches. Used combinational command \"cec\".\n" );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    // perform equivalence checking
    if ( fSat )
        Abc_NtkSecSat( pNtk1, pNtk2, nConfLimit, nInsLimit, nFrames );
    else
        Abc_NtkSecFraig( pNtk1, pNtk2, nSeconds, nFrames, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    fprintf( pErr, "usage: sec [-F num] [-T num] [-C num] [-I num] [-svh] <file1> <file2>\n" );
    fprintf( pErr, "\t         performs bounded sequential equivalence checking\n" );
    fprintf( pErr, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    fprintf( pErr, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pErr, "\t-h     : print the command usage\n");
    fprintf( pErr, "\t-F num : the number of time frames to use [default = %d]\n", nFrames );
    fprintf( pErr, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    fprintf( pErr, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    fprintf( pErr, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
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
int Abc_CommandSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    int RetValue;
    int fVerbose;
    int nConfLimit;
    int nInsLimit;
    int clk;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    fVerbose   = 0;
    nConfLimit = 100000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CIvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
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
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( stdout, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 

    clk = clock();
    if ( Abc_NtkIsStrash(pNtk) )
    {
        RetValue = Abc_NtkMiterSat( pNtk, (sint64)nConfLimit, (sint64)nInsLimit, fVerbose, NULL, NULL );
    }
    else
    {
        assert( Abc_NtkIsLogic(pNtk) );
        Abc_NtkLogicToBdd( pNtk );
        RetValue = Abc_NtkMiterSat( pNtk, (sint64)nConfLimit, (sint64)nInsLimit, fVerbose, NULL, NULL );
    }

    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        //int i;
        //Abc_Obj_t * pObj;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            printf( "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        free( pSimInfo );
        /*
        // print model
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            printf( "%d", (int)(pNtk->pModel[i] > 0) );
            if ( i == 70 )
                break;
        }
        printf( "\n" );
        */
    }

    if ( RetValue == -1 )
        printf( "UNDECIDED      " );
    else if ( RetValue == 0 )
        printf( "SATISFIABLE    " );
    else
        printf( "UNSATISFIABLE  " );
    //printf( "\n" );
    PRT( "Time", clock() - clk );
    return 0;

usage:
    fprintf( pErr, "usage: sat [-C num] [-I num] [-vh]\n" );
    fprintf( pErr, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    fprintf( pErr, "\t         derives CNF from the current network and leave it unchanged\n" );
    fprintf( pErr, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    fprintf( pErr, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
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
int Abc_CommandProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    Prove_Params_t Params, * pParams = &Params;
    int c, clk, RetValue;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set defaults
    Prove_ParamsSetDefault( pParams );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCFLIrfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nItersMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nItersMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitStart < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitLast = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitLast < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                fprintf( pErr, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nTotalInspectLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nTotalInspectLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            pParams->fUseRewriting ^= 1;
            break;
        case 'f':
            pParams->fUseFraiging ^= 1;
            break;
        case 'b':
            pParams->fUseBdds ^= 1;
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
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( stdout, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 
    if ( Abc_NtkCoNum(pNtk) != 1 )
    {
        fprintf( stdout, "Currently can only solve the miter with one output.\n" );
        return 0;
    } 
    clk = clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0 );

    RetValue = Abc_NtkMiterProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        if ( pSimInfo[0] != 1 )
            printf( "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        free( pSimInfo );
    }
 
    if ( RetValue == -1 ) 
        printf( "UNDECIDED      " );
    else if ( RetValue == 0 )
        printf( "SATISFIABLE    " );
    else
        printf( "UNSATISFIABLE  " );
    //printf( "\n" );

    PRT( "Time", clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    return 0;

usage:
    fprintf( pErr, "usage: prove [-N num] [-C num] [-F num] [-L num] [-I num] [-rfbvh]\n" );
    fprintf( pErr, "\t         solves combinational miter by rewriting, FRAIGing, and SAT\n" );
    fprintf( pErr, "\t         replaces the current network by the cone modified by rewriting\n" );
    fprintf( pErr, "\t-N num : max number of iterations [default = %d]\n", pParams->nItersMax );
    fprintf( pErr, "\t-C num : max starting number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitStart );
    fprintf( pErr, "\t-F num : max starting number of conflicts in fraiging [default = %d]\n", pParams->nFraigingLimitStart );
    fprintf( pErr, "\t-L num : max last-gasp number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitLast );
    fprintf( pErr, "\t-I num : max number of clause inspections in all SAT calls [default = %d]\n", (int)pParams->nTotalInspectLimit );
    fprintf( pErr, "\t-r     : toggle the use of rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );  
    fprintf( pErr, "\t-f     : toggle the use of FRAIGing [default = %s]\n", pParams->fUseFraiging? "yes": "no" );  
    fprintf( pErr, "\t-b     : toggle the use of BDDs [default = %s]\n", pParams->fUseBdds? "yes": "no" );  
    fprintf( pErr, "\t-v     : prints verbose information [default = %s]\n", pParams->fVerbose? "yes": "no" );  
    fprintf( pErr, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDebug( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;
    extern void Abc_NtkAutoDebug( Abc_Ntk_t * pNtk, int (*pFuncError) (Abc_Ntk_t *) );
    extern int Abc_NtkRetimeDebug( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( pErr, "This command is applicable to logic networks.\n" );
        return 1;
    }

    Abc_NtkAutoDebug( pNtk, Abc_NtkRetimeDebug );
    return 0;

usage:
    fprintf( pErr, "usage: debug [-h]\n" );
    fprintf( pErr, "\t        performs automated debugging of the given procedure\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTraceStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command is applicable to AIGs.\n" );
        return 1;
    }
/*
    Abc_HManStart();
    if ( !Abc_HManPopulate( pNtk ) )
    {
        fprintf( pErr, "Failed to start the tracing database.\n" );
        return 1;
    }
*/
    return 0;

usage:
    fprintf( pErr, "usage: trace_start [-h]\n" );
    fprintf( pErr, "\t        starts verification tracing\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTraceCheck( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pErr, "This command is applicable to AIGs.\n" );
        return 1;
    }
/*
    if ( !Abc_HManIsRunning(pNtk) )
    {
        fprintf( pErr, "The tracing database is not available.\n" );
        return 1;
    }

    if ( !Abc_HManVerify( 1, pNtk->Id ) )
        fprintf( pErr, "Verification failed.\n" );
    Abc_HManStop();
*/
    return 0;

usage:
    fprintf( pErr, "usage: trace_check [-h]\n" );
    fprintf( pErr, "\t        checks the current network using verification trace\n" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


