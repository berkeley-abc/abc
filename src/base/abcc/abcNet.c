/**CFile****************************************************************

  FileName    [abcNet.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Network conversion and editing.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "aig/gia/giaEdit.h"
#include "bool/kit/kit.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandStrash                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLogic                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandComb                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrPos                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAndPos                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandZeroPo                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSwapPos                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRemovePo               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDropSat                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAddPi                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAppend                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPutOnTop               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSop                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBdd                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAig                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrder                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCone                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNode                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRange                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCof                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTopmost                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBottommost             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTopAnd                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTrim                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShortNames             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMoveNames              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcFree               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcGet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcSet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCareSet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDouble                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBb2Wb                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOutdec                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNodeDup                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandWrap                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIStrash                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPermute                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnpermute              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MuxPos             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MuxStr             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MuxDec             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Rex2Gia            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Strash             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Topand             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cof                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cofs               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Trim               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dfs                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Times              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Append             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Posplit            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Permute            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cone               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Slice              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PoPart             ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandAbc9PoPart2            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PutOnTop           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Window             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AndCare            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Divide             ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );

/**Function*************************************************************

  Synopsis    [Registers network conversion and editing commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitNet( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "st",            Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "strash",        Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "logic",         Abc_CommandLogic,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "comb",          Abc_CommandComb,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "orpos",         Abc_CommandOrPos,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "andpos",        Abc_CommandAndPos,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "zeropo",        Abc_CommandZeroPo,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "swappos",       Abc_CommandSwapPos,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "removepo",      Abc_CommandRemovePo,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "dropsat",       Abc_CommandDropSat,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "addpi",         Abc_CommandAddPi,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "append",        Abc_CommandAppend,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "putontop",      Abc_CommandPutOnTop,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "sop",           Abc_CommandSop,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "bdd",           Abc_CommandBdd,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "aig",           Abc_CommandAig,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "order",         Abc_CommandOrder,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "cone",          Abc_CommandCone,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "node",          Abc_CommandNode,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "range",         Abc_CommandRange,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "cof",           Abc_CommandCof,              1 );
    Cmd_CommandAdd( pAbc, "Various",      "topmost",       Abc_CommandTopmost,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "bottommost",    Abc_CommandBottommost,       1 );
    Cmd_CommandAdd( pAbc, "Various",      "topand",        Abc_CommandTopAnd,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "trim",          Abc_CommandTrim,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "short_names",   Abc_CommandShortNames,       0 );
    Cmd_CommandAdd( pAbc, "Various",      "move_names",    Abc_CommandMoveNames,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_free",     Abc_CommandExdcFree,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_get",      Abc_CommandExdcGet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_set",      Abc_CommandExdcSet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "care_set",      Abc_CommandCareSet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "double",        Abc_CommandDouble,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "bb2wb",         Abc_CommandBb2Wb,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "outdec",        Abc_CommandOutdec,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "nodedup",       Abc_CommandNodeDup,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "wrap",          Abc_CommandWrap,             0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "istrash",       Abc_CommandIStrash,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "permute",       Abc_CommandPermute,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "unpermute",     Abc_CommandUnpermute,        1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&muxpos",       Abc_CommandAbc9MuxPos,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&muxstr",       Abc_CommandAbc9MuxStr,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&muxdec",       Abc_CommandAbc9MuxDec,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&rex2gia",      Abc_CommandAbc9Rex2Gia,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&st",           Abc_CommandAbc9Strash,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&topand",       Abc_CommandAbc9Topand,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cof",          Abc_CommandAbc9Cof,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cofs",         Abc_CommandAbc9Cofs,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&trim",         Abc_CommandAbc9Trim,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dfs",          Abc_CommandAbc9Dfs,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&times",        Abc_CommandAbc9Times,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&append",       Abc_CommandAbc9Append,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&posplit",      Abc_CommandAbc9Posplit,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&permute",      Abc_CommandAbc9Permute,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cone",         Abc_CommandAbc9Cone,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&slice",        Abc_CommandAbc9Slice,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&popart",       Abc_CommandAbc9PoPart,       0 );
//    Cmd_CommandAdd( pAbc, "ABC9",         "&popart2",      Abc_CommandAbc9PoPart2,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&putontop",     Abc_CommandAbc9PutOnTop,               0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&window",       Abc_CommandAbc9Window,                 0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&andcare",      Abc_CommandAbc9AndCare,                0 );   
    Cmd_CommandAdd( pAbc, "ABC9",         "&divide",       Abc_CommandAbc9Divide,                 0 );
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
int Abc_CommandStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pObj;
    int c;
    int fAllNodes;
    int fRecord;
    int fCleanup;
    int fComplOuts;
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fAllNodes = 0;
    fCleanup  = 1;
    fRecord   = 0;
    fComplOuts= 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "acrih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'c':
            fCleanup ^= 1;
            break;
        case 'r':
            fRecord ^= 1;
            break;
        case 'i':
            fComplOuts ^= 1;
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
    pNtkRes = Abc_NtkStrash( pNtk, fAllNodes, fCleanup, fRecord );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Strashing has failed.\n" );
        return 1;
    }
    if ( fComplOuts )
    Abc_NtkForEachPo( pNtkRes, pObj, c )
        Abc_ObjXorFaninC( pObj, 0 );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: strash [-acrih]\n" );
    Abc_Print( -2, "\t        transforms combinational logic into an AIG\n" );
    Abc_Print( -2, "\t-a    : toggles between using all nodes and DFS nodes [default = %s]\n", fAllNodes? "all": "DFS" );
    Abc_Print( -2, "\t-c    : toggles cleanup to remove the dangling AIG nodes [default = %s]\n", fCleanup? "all": "DFS" );
    Abc_Print( -2, "\t-r    : toggles using the record of AIG subgraphs [default = %s]\n", fRecord? "yes": "no" );
    Abc_Print( -2, "\t-i    : toggles complementing the POs of the AIG [default = %s]\n", fComplOuts? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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

    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        Abc_Print( -1, "This command is only applicable to strashed networks.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkToLogic( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to a logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: logic [-h]\n" );
    Abc_Print( -2, "\t        transforms an AIG into a logic network with SOPs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRemoveLatches;
    int nLatchesToAdd;
    extern void Abc_NtkMakeSeq( Abc_Ntk_t * pNtk, int nLatchesToAdd );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRemoveLatches = 0;
    nLatchesToAdd = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Llh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLatchesToAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLatchesToAdd < 0 )
                goto usage;
            break;
        case 'l':
            fRemoveLatches ^= 1;
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
    if ( Abc_NtkIsComb(pNtk) && nLatchesToAdd == 0 )
    {
        Abc_Print( -1, "The network is already combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsComb(pNtk) && nLatchesToAdd != 0 )
    {
        Abc_Print( -1, "The network is already combinational.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    if ( nLatchesToAdd )
        Abc_NtkMakeSeq( pNtkRes, nLatchesToAdd );
    else
        Abc_NtkMakeComb( pNtkRes, fRemoveLatches );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: comb [-L <num>] [-lh]\n" );
    Abc_Print( -2, "\t           converts comb network into seq, and vice versa\n" );
    Abc_Print( -2, "\t-L <num> : number of latches to add to comb network (0 = do not add) [default = %d]\n", nLatchesToAdd );
    Abc_Print( -2, "\t-l       : toggle converting latches to PIs/POs or removing them [default = %s]\n", fRemoveLatches? "remove": "convert" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes;
    int fReverse = 0;
    int fComb = 0;
    int fXor = 0;
    int c;
    extern int Abc_NtkCombinePos( Abc_Ntk_t * pNtk, int fAnd, int fXor );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rxh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fReverse ^= 1;
            break;
        case 'x':
            fXor ^= 1;
            break;
        case 'c':
            fComb ^= 1;
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
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    // get the new network
    if ( fReverse )
    {
        extern Aig_Man_t * Abc_NtkToDarBmc( Abc_Ntk_t * pNtk, Vec_Int_t ** pvMap );
        Aig_Man_t * pMan = Abc_NtkToDarBmc( pNtk, NULL );
        Abc_Ntk_t * pNtkRes = Abc_NtkFromAigPhase( pMan );
        Aig_ManStop( pMan );
        // perform expansion
        if ( Abc_NtkPoNum(pNtk) != Abc_NtkPoNum(pNtkRes) )
            Abc_Print( 1,"Expanded %d outputs into %d outputs using OR decomposition.\n", Abc_NtkPoNum(pNtk), Abc_NtkPoNum(pNtkRes) );
        else
            Abc_Print( 1,"The output(s) cannot be structurally decomposed.\n" );
        // clear counter-example
        if ( pAbc->pCex )
            ABC_FREE( pAbc->pCex );
        // replace the current network
        ABC_FREE( pNtkRes->pName );
        pNtkRes->pName = Extra_UtilStrsav(pNtk->pName);
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    else
    {
        if ( !Abc_NtkCombinePos( pNtk, 0, fXor ) )
        {
            Abc_Print( -1, "ORing the POs has failed.\n" );
            return 1;
        }
        // update counter-example
        if ( pAbc->pCex )
            pAbc->pCex->iPo = 0;
        // replace the current network
    //    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: orpos [-rxh]\n" );
    Abc_Print( -2, "\t        creates single-output miter by ORing the POs of the current network\n" );
    Abc_Print( -2, "\t-r    : performs the reverse transform (OR decomposition) [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-x    : toggles combining the PO using XOR [default = %s]\n", fXor? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes;
    int fComb = 0;
    int c;

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

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }

    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        Abc_Print( -1, "The network already has one PO.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The miter has latches. ORing is not performed.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkCombinePos( pNtk, 1, 0 ) )
    {
        Abc_Print( -1, "ANDing the POs has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: andpos [-h]\n" );
    Abc_Print( -2, "\t        creates single-output miter by ANDing the POs of the current network\n" );
//    Abc_Print( -2, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandZeroPo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes = NULL;
    int c, iOutput = -1;
    int fSkipSweep = 0;
    int fUseConst1 = 0;
    extern void Abc_NtkDropOneOutput( Abc_Ntk_t * pNtk, int iOutput, int fSkipSweep, int fUseConst1 );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nsoh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 )
                goto usage;
            break;
        case 's':
            fSkipSweep ^= 1;
            break;
        case 'o':
            fUseConst1 ^= 1;
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
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkDup( pNtk );
//    Abc_NtkDropOneOutput( pNtkRes, iOutput );
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    Abc_NtkDropOneOutput( pNtk, iOutput, fSkipSweep, fUseConst1 );
    return 0;

usage:
    Abc_Print( -2, "usage: zeropo [-N <num>] [-soh]\n" );
    Abc_Print( -2, "\t           replaces the PO driver by constant 0\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to replace [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-s       : performs comb sweep after removimg a PO [default = %s]\n", !fSkipSweep? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles using const 1 instead of const 0 [default = %s]\n", fUseConst1? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSwapPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c, iOutput = -1;
    extern void Abc_NtkSwapOneOutput( Abc_Ntk_t * pNtk, int iOutput );

    // set defaults
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
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 )
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
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_NtkSwapOneOutput( pNtkRes, iOutput );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: swappos [-N <num>] [-h]\n" );
    Abc_Print( -2, "\t           swap the 0-th PO with the <num>-th PO\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to swap [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRemovePo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes = NULL;
    int c, iOutput = -1;
    int fRemoveConst0 = 1;
    extern void Abc_NtkRemovePo( Abc_Ntk_t * pNtk, int iOutput, int fRemoveConst0 );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nzh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 )
                goto usage;
            break;
        case 'z':
            fRemoveConst0 ^= 1;
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
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkDup( pNtk );
//    Abc_NtkRemovePo( pNtkRes, iOutput );
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    Abc_NtkRemovePo( pNtk, iOutput, fRemoveConst0 );
    return 0;

usage:
    Abc_Print( -2, "usage: removepo [-N <num>] [-zh]\n" );
    Abc_Print( -2, "\t           remove PO with number <num> if it is const0\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to remove [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-z       : toggle removing const1 instead of const0 [default = %s]\n", fRemoveConst0? "const0": "const1" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDropSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkDropSatOutputs( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCexes, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes = NULL;
    int fNoSweep = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fNoSweep ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
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
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( pAbc->vCexVec == NULL )
    {
        Abc_Print( -1, "CEX array is not defined. Run \"bmc3 -az\", \"sim3 -az\", or \"pdr -az\".\n" );
        return 1;
    }
    if ( Vec_PtrSize(pAbc->vCexVec) != Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "CEX array size (%d) does not match the number of outputs (%d).\n", Vec_PtrSize(pAbc->vCexVec), Abc_NtkPoNum(pNtk) );
        return 1;
    }
    Abc_NtkDropSatOutputs( pNtk, pAbc->vCexVec, fVerbose );
    if ( !fNoSweep )
    {
        pNtkRes = Abc_NtkDarLatchSweep( pNtk, 1, 1, 1, 0, -1, -1, 0, 0 );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Removing SAT outputs has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dropsat [-sh]\n" );
    Abc_Print( -2, "\t         replaces satisfiable POs by constant 0 and cleans up the AIG\n" );
    Abc_Print( -2, "\t-s     : toggles skipping sequential sweep [default = %s]\n", fNoSweep? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAddPi( Abc_Frame_t * pAbc, int argc, char ** argv )
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

    // get the new network
    if ( Abc_NtkPiNum(pNtk) == 0 )
    {
        Abc_Ntk_t * pNtkRes = Abc_NtkDup( pNtk );
        Abc_Obj_t * pObj = Abc_NtkCreatePi( pNtkRes );
        Abc_ObjAssignName( pObj, "dummy_pi", NULL );
        Abc_NtkOrderCisCos( pNtkRes );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: addpi [-h]\n" );
    Abc_Print( -2, "\t         if the network has no PIs, add one dummy PI\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    Abc_Ntk_t * pNtk, * pNtk2;
    char * FileName;
    int fComb = 0;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

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
        Abc_Print( -1, "The network to append is not given.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The base network should be strashed for the appending to work.\n" );
        return 1;
    }

    // read the second network
    FileName = argv[globalUtilOptind];
    pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
    if ( pNtk2 == NULL )
        return 1;

    // check if the second network is combinational
    if ( Abc_NtkLatchNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The second network has latches. Appending does not work for such networks.\n" );
        return 0;
    }

    // get the new network
    if ( !Abc_NtkAppend( pNtk, pNtk2, 1 ) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "Appending the networks failed.\n" );
        return 1;
    }
    Abc_NtkDelete( pNtk2 );
    // sweep dangling logic
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: append [-h] <file>\n" );
    Abc_Print( -2, "\t         appends a combinational network on top of the current network\n" );
//    Abc_Print( -2, "\t-c     : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name with the second network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPutOnTop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkPutOnTop( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtk2 );

    Abc_Ntk_t * pNtk, * pNtk2, * pNtkRes = NULL;
    char * FileName;
    int fComb = 0;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

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

    if ( argc > globalUtilOptind + 1 )
    {
        for ( c = 1; c < argc; c++ )
        {
            Abc_Ntk_t * pTemp, * pLogic = Io_Read( argv[c], Io_ReadFileType(argv[c]), 1, 0 );
            if ( pLogic == NULL )
                return 1;
            if ( Abc_NtkIsStrash(pLogic) )
            {
                pLogic = Abc_NtkToLogic( pTemp = pLogic );
                Abc_NtkDelete( pTemp );
            }
            if ( pLogic == NULL )
                return 1;
            if ( pNtkRes == NULL )
                pNtkRes = pLogic;
            else
            {
                pNtkRes = Abc_NtkPutOnTop( pTemp = pNtkRes, pLogic );
                Abc_NtkDelete( pTemp );
                Abc_NtkDelete( pLogic );
                if ( pNtkRes == NULL )
                    return 1;
            }
        }
        assert( Abc_NtkIsLogic(pNtkRes) );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }

    // get the second network
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "The network to append is not given.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "The base network should be in the logic form.\n" );
        return 1;
    }

    // check if the second network is combinational
    if ( Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The current network has latches. This command does not work for such networks.\n" );
        return 0;
    }

    // read the second network
    FileName = argv[globalUtilOptind];
    pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
    if ( pNtk2 == NULL )
        return 1;

    // check if the second network is combinational
    if ( Abc_NtkLatchNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The second network has latches. This command does not work for such networks.\n" );
        return 0;
    }
    // compare inputs/outputs
    if ( Abc_NtkPoNum(pNtk) != Abc_NtkPiNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The PO count (%d) of the first network is not equal to PI count (%d) of the second network.\n", Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk2) );
        return 0;
    }

    // get the new network
    if ( Abc_NtkIsLogic(pNtk2) )
        pNtkRes = Abc_NtkPutOnTop( pNtk, pNtk2 );
    else if ( Abc_NtkIsStrash(pNtk2) )
    {
        Abc_Ntk_t * pLogic = Abc_NtkToLogic( pNtk2 );
        pNtkRes = Abc_NtkPutOnTop( pNtk, pLogic );
        Abc_NtkDelete( pLogic );
    }
    else assert( 0 );
    Abc_NtkDelete( pNtk2 );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: putontop [-h] <file>\n" );
    Abc_Print( -2, "\t         connects PIs of network in <file> to POs of current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name with the second network\n");
    Abc_Print( -2, "\t       : (given several files, all networks are stacked on top of each other)\n");
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
    extern void Abc_NtkFaninSort( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fCubeSort = 1, fMode = -1, nCubeLimit = 1000000;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Csdnh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCubeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCubeLimit < 0 )
                goto usage;
            break;
        case 's':
            fCubeSort ^= 1;
            break;
        case 'd':
            fMode = 1;
            break;
        case 'n':
            fMode = 0;
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
        Abc_Print( -1, "Converting to SOP is possible only for logic networks.\n" );
        return 1;
    }
    if ( fCubeSort && Abc_NtkHasSop(pNtk) )
    {
        Abc_NtkSortSops(pNtk);
        return 0;
    }
    if ( !fCubeSort && Abc_NtkHasBdd(pNtk) && !Abc_NtkBddToSop(pNtk, -1, ABC_INFINITY, 0) )
    {
        Abc_Print( -1, "Converting to SOP has failed.\n" );
        return 0;
    }
    if ( !Abc_NtkToSop(pNtk, fMode, nCubeLimit) )
    {
        Abc_Print( -1, "Converting to SOP has failed.\n" );
        return 0;
    }
    if ( !fCubeSort )
        Abc_NtkFaninSort( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: sop [-C num] [-sdnh]\n" );
    Abc_Print( -2, "\t         converts node functions to SOP\n" );
    Abc_Print( -2, "\t-C num : the limit on the number of cubes at a node [default = %d]\n", nCubeLimit );
    Abc_Print( -2, "\t-s     : toggles cube sort when converting from BDDs [default = %s]\n", fCubeSort ? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggles using only positive polarity [default = %s]\n", fMode == 1 ? "yes": "no"  );
    Abc_Print( -2, "\t-n     : toggles using only negative polarity [default = %s]\n", fMode == 0 ? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fReorder = 1, fBdd2Sop = 0;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fReorder ^= 1;
            break;
        case 's':
            fBdd2Sop ^= 1;
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
        Abc_Print( -1, "Converting to BDD is possible only for logic networks.\n" );
        return 1;
    }
    if ( fBdd2Sop && Abc_NtkHasSop(pNtk) )
        return !Abc_NtkSopToBdd(pNtk);
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "The logic network is already in the BDD form.\n" );
        return 0;
    }
    if ( !Abc_NtkToBdd(pNtk) )
    {
        Abc_Print( -1, "Converting to BDD has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: bdd [-rsh]\n" );
    Abc_Print( -2, "\t         converts node functions to BDD\n" );
    Abc_Print( -2, "\t-r     : toggles enabling dynamic variable reordering [default = %s]\n", fReorder? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles constructing BDDs directly from SOPs [default = %s]\n", fBdd2Sop? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Converting to AIG is possible only for logic networks.\n" );
        return 1;
    }
    if ( Abc_NtkIsAigLogic(pNtk) )
    {
        Abc_Print( -1, "The logic network is already in the AIG form.\n" );
        return 0;
    }
    if ( !Abc_NtkToAig(pNtk) )
    {
        Abc_Print( -1, "Converting to AIG has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: aig [-h]\n" );
    Abc_Print( -2, "\t         converts node functions to AIG\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    FILE * pFile;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    char * pFileName;
    int c;
    int fReverse;
    int fVerbose;
    extern void Abc_NtkImplementCiOrder( Abc_Ntk_t * pNtk, char * pFileName, int fReverse, int fVerbose );
    extern void Abc_NtkFindCiOrder( Abc_Ntk_t * pNtk, int fReverse, int fVerbose );

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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
//    if ( Abc_NtkLatchNum(pNtk) > 0 )
//    {
//        Abc_Print( -1, "Currently this procedure does not work for sequential networks.\n" );
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
            Abc_Print( -1, "Cannot open file \"%s\" with the BDD variable order.\n", pFileName );
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
    Abc_Print( -2, "usage: order [-rvh] <file>\n" );
    Abc_Print( -2, "\t         computes a good static CI variable order\n" );
    Abc_Print( -2, "\t-r     : toggle reverse ordering [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : (optional) file with the given variable order\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads a separated list of integers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Vec_IntReadList( char * pStr, char Separ )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 10 );
    Vec_IntPush( vRes, atoi(pStr) );
    for ( int c = 0; c < strlen(pStr); c++ )
        if ( pStr[c] == Separ )
            Vec_IntPush( vRes, atoi(pStr+c+1) );
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCone( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode, * pNodeCo;
    Vec_Int_t * vPoIds = NULL;
    int c;
    int fUseAllCis;
    int fUseMffc;
    int Output;
    int nRange;

    extern Abc_Ntk_t * Abc_NtkSelectPos( Abc_Ntk_t * pNtkInit, Vec_Int_t * vPoIds );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUseAllCis = 0;
    fUseMffc = 0;
    Output = -1;
    nRange = -1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ORNmah" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRange = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRange < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            vPoIds = Vec_IntReadList( argv[globalUtilOptind], ',' );
            globalUtilOptind++;
            if ( vPoIds == NULL )
                goto usage;
            break;
        case 'm':
            fUseMffc ^= 1;
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently can only be applied to the logic network or an AIG.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNodeCo = NULL;
    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        c = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind], ABC_OBJ_PO );
        if ( c < 0 )
            c = Nm_ManFindIdByName( pNtk->pManName, argv[globalUtilOptind], ABC_OBJ_BI );
        if ( c >= 0 )
            pNodeCo = Abc_NtkObj( pNtk, c );
        if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, pNode, argv[globalUtilOptind] );
        else
            pNtkRes = Abc_NtkCreateCone( pNtk, pNode, argv[globalUtilOptind], fUseAllCis );
    }
    else if ( vPoIds )
    {
        pNtkRes = Abc_NtkSelectPos( pNtk, vPoIds );
        Vec_IntFree( vPoIds );
    }
    else if ( nRange > 0 )
    {
        if ( Output == -1 )
        {
            Abc_Print( -1, "The starting PO ID is not specified.\n" );
            return 1;
        }        
        if ( Output >= Abc_NtkPoNum(pNtk) )
        {
            Abc_Print( -1, "The 0-based output number (%d) is larger than the number of primary outputs (%d).\n", Output, Abc_NtkPoNum(pNtk) );
            return 1;
        }        assert( vPoIds == NULL );
        vPoIds = Vec_IntAlloc( nRange );
        for ( c = Output; c < Output + nRange; c++ )
            Vec_IntPush( vPoIds, c );
        pNtkRes = Abc_NtkSelectPos( pNtk, vPoIds );
        Vec_IntFree( vPoIds );
    }
    else if ( Output >= 0 )
    {
        if ( Output >= Abc_NtkPoNum(pNtk) )
        {
            Abc_Print( -1, "The 0-based output number (%d) is larger than the number of primary outputs (%d).\n", Output, Abc_NtkPoNum(pNtk) );
            return 1;
        }        assert( vPoIds == NULL );
        vPoIds = Vec_IntAlloc( 1 );
        Vec_IntPush( vPoIds, Output );
        pNtkRes = Abc_NtkSelectPos( pNtk, vPoIds );
        Vec_IntFree( vPoIds );
    }
    else
    {
        if ( Output == -1 )
        {
            Abc_Print( -1, "The starting PO ID is not specified.\n" );
            return 1;
        }
        if ( Output >= Abc_NtkCoNum(pNtk) )
        {
            Abc_Print( -1, "The 0-based output number (%d) is larger than the number of combinational outputs (%d).\n", Output, Abc_NtkCoNum(pNtk) );
            return 1;
        }
        pNodeCo = Abc_NtkCo( pNtk, Output );
        if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo) );
        else
            pNtkRes = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo), fUseAllCis );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Writing the logic cone of one node has failed.\n" );
        return 1;
    }
    if ( pNodeCo && Abc_ObjFaninC0(pNodeCo) )
        Abc_NtkPo(pNtkRes, 0)->fCompl0 ^= 1;
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cone [-ORN num] [-amh] <name>\n" );
    Abc_Print( -2, "\t         replaces the current network by one or more logic cones\n" );
    Abc_Print( -2, "\t-a     : toggle keeping all CIs or structral support only [default = %s]\n", fUseAllCis? "all": "structural" );
    Abc_Print( -2, "\t-m     : toggle keeping only MFFC or complete TFI cone [default = %s]\n", fUseMffc? "MFFC": "TFI cone" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-O num : (optional) the 0-based number of the CO to extract\n");
    Abc_Print( -2, "\t-R num : (optional) the number of outputs to extract\n");
    Abc_Print( -2, "\t-N <list> : (optional) a comma-separated list of zero-based primary output indexes\n");
    Abc_Print( -2, "\tname   : (optional) the name of the node to extract\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode;
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

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Currently can only be applied to a logic network.\n" );
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

    pNtkRes = Abc_NtkCreateFromNode( pNtk, pNode );
//    pNtkRes = Abc_NtkDeriveFromBdd( pNtk->pManFunc, pNode->pData, NULL, NULL );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Splitting one node has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: node [-h] <name>\n" );
    Abc_Print( -2, "\t         replaces the current network by the network composed of one node\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRange( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);
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
        Abc_Print( -1, "Currently can only be applied to an AIG.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkCreateFromRange( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Deriving the network has failed.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: range [-h]\n" );
    Abc_Print( -2, "\t         computes the range of output values as one node\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCof( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    int c, Const;

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

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Currently can only be applied to a logic network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    pNode = Abc_NtkFindCi( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
        return 1;
    }
    Const = atoi( argv[globalUtilOptind+1] );
    if ( Const != 0 && Const != 1 )
    {
        Abc_Print( -1, "Constant should be 0 or 1.\n", argv[globalUtilOptind+1] );
        return 1;
    }
    Abc_ObjReplaceByConstant( pNode, Const );
    return 0;

usage:
    Abc_Print( -2, "usage: cof [-h] <node> <const>\n" );
    Abc_Print( -2, "\t          replaces one node in a logic network by constant 0 or 1\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<node>  : the node to replace\n");
    Abc_Print( -2, "\t<const> : the constant to replace the node with\n");
    Abc_Print( -2, "\tname    : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTopmost( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLevels;
    extern Abc_Ntk_t * Abc_NtkTopmost( Abc_Ntk_t * pNtk, int nLevels );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nLevels = 10;
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

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently only works for combinational circuits.\n" );
        return 0;
    }

    pNtkRes = Abc_NtkTopmost( pNtk, nLevels );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: topmost [-N num] [-h]\n" );
    Abc_Print( -2, "\t         replaces the current network by several of its topmost levels\n" );
    Abc_Print( -2, "\t-N num : max number of levels [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBottommost( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLevels;
    extern Abc_Ntk_t * Abc_NtkBottommost( Abc_Ntk_t * pNtk, int nLevels );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nLevels = 10;
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

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently only works for combinational circuits.\n" );
        return 0;
    }

    pNtkRes = Abc_NtkBottommost( pNtk, nLevels );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: bottommost [-N num] [-h]\n" );
    Abc_Print( -2, "\t         replaces the current network by several of its bottommost levels\n" );
    Abc_Print( -2, "\t-N num : max number of levels [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTopAnd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkTopAnd( Abc_Ntk_t * pNtk );

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
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only works for combinational circuits.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently expects a single-output miter.\n" );
        return 0;
    }
    if ( Abc_ObjFaninC0(Abc_NtkPo(pNtk, 0)) )
    {
        Abc_Print( -1, "The PO driver is complemented. AND-decomposition is impossible.\n" );
        return 0;
    }
    if ( !Abc_ObjIsNode(Abc_ObjChild0(Abc_NtkPo(pNtk, 0))) )
    {
        Abc_Print( -1, "The PO driver is not a node. AND-decomposition is impossible.\n" );
        return 0;
    }
    pNtkRes = Abc_NtkTopAnd( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: topand [-h]\n" );
    Abc_Print( -2, "\t         performs AND-decomposition of single-output combinational miter\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTrim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Gia_Man_t * pGia, * pNew;
    Aig_Man_t * pAig;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
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
        Abc_Print( -1, "Trimming works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    // convert to GIA
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    pGia = Gia_ManFromAigSimple( pAig );
    Aig_ManStop( pAig );
    // perform trimming
    pNew = Gia_ManDupTrimmed( pGia, 1, 1, 0, -1 );
    Gia_ManStop( pGia );
    // convert back
    pAig = Gia_ManToAigSimple( pNew );
    Gia_ManStop( pNew );
    pNtkRes = Abc_NtkFromAigPhase( pAig );
    Aig_ManStop( pAig );
    // duplicate the name and the spec
    ABC_FREE( pNtkRes->pName );
    ABC_FREE( pNtkRes->pSpec );
    pNtkRes->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkRes->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: trim [-h]\n" );
    Abc_Print( -2, "\t         removes POs fed by constants and PIs w/o fanout\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fKeepIo = 0, fAlpha = 0;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "akh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAlpha ^= 1;
            break;
        case 'k':
            fKeepIo ^= 1;
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
    if ( fAlpha )
        Abc_NtkCharNames( pNtk );
    else if ( fKeepIo )
        Abc_NtkCleanNames( pNtk );
    else
        Abc_NtkShortNames( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: short_names [-akh]\n" );
    Abc_Print( -2, "\t         replaces PI/PO/latch names by short char strings\n" );
    Abc_Print( -2, "\t-a     : toggle using simple character names for PIs/POs [default = %s]\n", fAlpha? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle keeping PI/PO names unchanged [default = %s]\n", fKeepIo? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMoveNames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkMoveNames( Abc_Ntk_t * pNtk, Abc_Ntk_t * pOld );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtk2;
    char * FileName;
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

    // get the second network
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "The network to take names from is not given.\n" );
        return 1;
    }

    // read the second network
    FileName = argv[globalUtilOptind];
    pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
    if ( pNtk2 == NULL )
        return 1;

    // compare inputs/outputs
    if ( Abc_NtkPiNum(pNtk) != Abc_NtkPiNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The PI count (%d) of the first network is not equal to PI count (%d) of the second network.\n", Abc_NtkPiNum(pNtk), Abc_NtkPiNum(pNtk2) );
        return 0;
    }
    // compare inputs/outputs
    if ( Abc_NtkPoNum(pNtk) != Abc_NtkPoNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The PO count (%d) of the first network is not equal to PO count (%d) of the second network.\n", Abc_NtkPoNum(pNtk), Abc_NtkPoNum(pNtk2) );
        return 0;
    }
    // compare inputs/outputs
    if ( Abc_NtkLatchNum(pNtk) != Abc_NtkLatchNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The flop count (%d) of the first network is not equal to flop count (%d) of the second network.\n", Abc_NtkLatchNum(pNtk), Abc_NtkLatchNum(pNtk2) );
        return 0;
    }
    Abc_NtkMoveNames( pNtk, pNtk2 );
    Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: move_names [-h] <file>\n" );
    Abc_Print( -2, "\t         moves PI/PO/latch names from the other network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file with network that has required names\n");
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
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "The network has no EXDC.\n" );
        return 1;
    }

    Abc_NtkDelete( pNtk->pExdc );
    pNtk->pExdc = NULL;

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: exdc_free [-h]\n" );
    Abc_Print( -2, "\t         frees the EXDC network of the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "The network has no EXDC.\n" );
        return 1;
    }

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk->pExdc );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: exdc_get [-h]\n" );
    Abc_Print( -2, "\t         replaces the current network by the EXDC of the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    FILE * pFile;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    char * FileName;
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

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
    if ( pNtkNew == NULL )
    {
        Abc_Print( -1, "Reading network from file has failed.\n" );
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
    Abc_Print( -2, "usage: exdc_set [-h] <file>\n" );
    Abc_Print( -2, "\t         sets the network from file as EXDC for the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file with the new EXDC network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCareSet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    char * FileName;
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

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( FileName, Io_ReadFileType(FileName), 1, 0 );
    if ( pNtkNew == NULL )
    {
        Abc_Print( -1, "Reading network from file has failed.\n" );
        return 1;
    }

    // replace the EXDC
    if ( pNtk->pExcare )
    {
        Abc_NtkDelete( (Abc_Ntk_t *)pNtk->pExcare );
        pNtk->pExcare = NULL;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    pNtkRes->pExcare = pNtkNew;

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: care_set [-h] <file>\n" );
    Abc_Print( -2, "\t         sets the network from file as a care for the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file with the new care network\n");
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
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFrames;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDouble( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
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
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only works for logic SOP networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDouble( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: double [-vh]\n" );
    Abc_Print( -2, "\t         puts together two parallel copies of the current network\n" );
//    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
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
int Abc_CommandBb2Wb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkConvertBb2Wb( char * pFileNameIn, char * pFileNameOut, int fSeq, int fVerbose );
    int c;
    int fSeq;
    int fVerbose;
    // set defaults
    fSeq = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSeq ^= 1;
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
    Abc_NtkConvertBb2Wb( argv[globalUtilOptind], argv[globalUtilOptind+1], fSeq, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: bb2wb [-svh] <file_in> <file_out>\n" );
    Abc_Print( -2, "\t             replaces black boxes by white boxes with AND functions\n" );
    Abc_Print( -2, "\t             (file names should have standard extensions, e.g. \"blif\")\n" );
    Abc_Print( -2, "\t-s         : toggle using sequential white boxes [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-v         : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h         : print the command usage\n");
    Abc_Print( -2, "\t<file_in>  : input file with design containing black boxes\n");
    Abc_Print( -2, "\t<file_out> : output file with design containing white boxes\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOutdec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkDarOutdec( Abc_Ntk_t * pNtk, int nLits, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int c, nLits = 1;
    int fVerbose = 0;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLits < 1 || nLits > 2 )
            {
                Abc_Print( 1,"Currently, command \"outdec\" works for 1-lit and 2-lit primes only.\n" );
                goto usage;
            }
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
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDarOutdec( pNtk, nLits, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: outdec [-Lvh]\n" );
    Abc_Print( -2, "\t         performs prime decomposition of the first output\n" );
    Abc_Print( -2, "\t-L num : the number of literals in the primes [default = %d]\n", nLits );
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
int Abc_CommandNodeDup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkNodeDup( Abc_Ntk_t * pNtk, int nLimit, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int c, nLimit = 30;
    int fVerbose = 0;

    // set defaults
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
            nLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
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
        Abc_Print( -1, "Only works for logic networks.\n" );
        return 1;
    }
    if ( nLimit < 2 )
    {
        Abc_Print( -1, "The fanout limit should be more than 1.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkNodeDup( pNtk, nLimit, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: nodedup [-Nvh]\n" );
    Abc_Print( -2, "\t         duplicates internal nodes with high fanout\n" );
    Abc_Print( -2, "\t-N num : the number of fanouts to start duplication [default = %d]\n", nLimit );
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
int Abc_CommandWrap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName = NULL, * pFileName2 = NULL;
    FILE * pFile = NULL, * pFile2 = NULL;
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
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( 1,"Two file names are expected on the command line.\n" );
        return 0;
    }
    pFileName  = argv[globalUtilOptind];
    pFileName2 = argv[globalUtilOptind+1];
    pFile  = fopen( pFileName, "rb" );
    pFile2 = fopen( pFileName2, "wb" );
    if ( pFile && pFile2 )
    {
        char Buffer[1000];
        while ( fgets( Buffer, 1000, pFile ) != NULL )
        {
            if ( Buffer[strlen(Buffer)-1] == '\n' )
                Buffer[strlen(Buffer)-1] = 0;            
            if ( Buffer[strlen(Buffer)-1] == '\r' )
                Buffer[strlen(Buffer)-1] = 0;
            fprintf( pFile2, "  printf(\"%s\\n\");\n", Buffer );
        }
    }
    if ( pFile  ) fclose(pFile);   
    if ( pFile2 ) fclose(pFile2);   
    return 0;

usage:
    Abc_Print( -2, "usage: wrap [-h] <file> <file2>\n" );
    Abc_Print( -2, "\t           wrapping lines\n" );
    Abc_Print( -2, "\t<file>   : input text file\n");
    Abc_Print( -2, "\t<file2>  : output text file\n");    
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
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    extern Abc_Ntk_t * Abc_NtkIvyStrash( Abc_Ntk_t * pNtk );

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
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 1, 0 );
        pNtkRes = Abc_NtkIvyStrash( pNtkTemp );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes = Abc_NtkIvyStrash( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: istrash [-h]\n" );
    Abc_Print( -2, "\t         perform sequential structural hashing\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPermute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkRestrashRandom( Abc_Ntk_t * pNtk );
    extern void Abc_NtkPermutePiUsingFanout( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pNtk = pAbc->pNtkCur, * pNtkRes = NULL;
    char * pFlopPermFile = NULL, * pInPermFile = NULL, * pOutPermFile = NULL, * pMapPermFile = NULL;
    int fInputs = 1;
    int fOutputs = 1;
    int fFlops = 1;
    int fNodes = 1;
    int fFanout = 0;
    int Seed = -1;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SIOFMiofnxh" ) ) != EOF )
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a file name.\n" );
                goto usage;
            }
            pInPermFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by a file name.\n" );
                goto usage;
            }
            pOutPermFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFlopPermFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a file name.\n" );
                goto usage;
            }
            pMapPermFile = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'i':
            fInputs ^= 1;
            break;
        case 'o':
            fOutputs ^= 1;
            break;
        case 'f':
            fFlops ^= 1;
            break;
        case 'n':
            fNodes ^= 1;
            break;
        case 'x':
            fFanout ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( Seed >= 0 )
        srand( (unsigned)Seed );
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( fFanout )
    {
        if ( Abc_NtkLatchNum(pNtk) )
        {
            Abc_Print( -1, "Currently \"permute -x\" works only for combinational networks.\n" );
            return 1;
        }
        Abc_NtkPermutePiUsingFanout( pNtk );
        return 0;
    }
    if ( fNodes && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "To permute nodes, the network should be structurally hashed.\n" );
        return 1;
    }
    if ( fNodes ) {
        pNtkRes = Abc_NtkRestrashRandom( pNtk );
        if ( pMapPermFile ) {
            if ( Abc_NtkObjNumMax(pNtkRes) != Abc_NtkObjNumMax(pNtk) ) {
                printf( "Cannot output 1-to-1 node mapping because the networks have different node counts.\n" );
                return 1;
            }
            FILE * pFile = fopen( pMapPermFile, "wb" );
            if ( pFile == NULL ) {
                printf( "Cannot open output file \"%s\" to dump the permutation of internal nodes.\n", pMapPermFile );
                return 1;
            }
            Abc_Obj_t * pObj; int i, iNode, Counter = 0;
            int StartOld = Abc_NtkObjNumMax(pNtk)    - Abc_NtkNodeNum(pNtk);
            int StartNew = Abc_NtkObjNumMax(pNtkRes) - Abc_NtkNodeNum(pNtkRes);
            Abc_NtkForEachNode( pNtk, pObj, i ) {
                if ( Counter++ != i - StartOld ) {
                    printf( "Cannot output 1-to-1 node mapping because node order is non-standard.\n" );
                    fclose( pFile );
                    return 1;
                }
                iNode = pObj->pCopy->Id - StartNew;
                if ( iNode < 0 || iNode >= Abc_NtkNodeNum(pNtkRes) ) {
                    printf( "Cannot output 1-to-1 node mapping because node IDs are out of order.\n" );
                    fclose( pFile );
                    return 1;
                }
                fprintf( pFile, "%d ", iNode+1 );
            }
            fprintf( pFile, "\n" );
            fclose( pFile );
            printf( "Finished dumping the permutation of internal nodes into file \"%s\".\n", pMapPermFile );
        }
    }
    else
        pNtkRes = Abc_NtkDup( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command \"permute\" has failed.\n" );
        return 1;
    }
    Abc_NtkPermute( pNtkRes, fInputs, fOutputs, fFlops, pInPermFile, pOutPermFile, pFlopPermFile );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: permute [-S num] [-iofnxh] [-I filename] [-O filename] [-F filename] [-M filename]\n" );
    Abc_Print( -2, "\t                performs random permutation of inputs/outputs/flops\n" );
    Abc_Print( -2, "\t-S num        : the random seed to generate permutations (0 <= num < INT_MAX) [default = %d]\n", Seed );
    Abc_Print( -2, "\t-i            : toggle permuting primary inputs [default = %s]\n", fInputs? "yes": "no" );
    Abc_Print( -2, "\t-o            : toggle permuting primary outputs [default = %s]\n", fOutputs? "yes": "no" );
    Abc_Print( -2, "\t-f            : toggle permuting flip-flops [default = %s]\n", fFlops? "yes": "no" );
    Abc_Print( -2, "\t-n            : toggle deriving new topological ordering of nodes [default = %s]\n", fNodes? "yes": "no" );
    Abc_Print( -2, "\t-x            : toggle permuting inputs based on their fanout count [default = %s]\n", fFanout? "yes": "no" );
    Abc_Print( -2, "\t-h            : print the command usage\n");
    Abc_Print( -2, "\t-I <filename> : (optional) file with the input permutation\n" );
    Abc_Print( -2, "\t-O <filename> : (optional) file with the output permutation\n" );
    Abc_Print( -2, "\t-F <filename> : (optional) file with the flop permutation\n" );
    Abc_Print( -2, "\t-M <filename> : (optional) file with the resulting permutation of internal nodes\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnpermute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = pAbc->pNtkCur, * pNtkRes = NULL;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command \"unpermute\" has failed.\n" );
        return 1;
    }
    Abc_NtkUnpermute( pNtkRes );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: unpermute [-h]\n" );
    Abc_Print( -2, "\t        restores inputs/outputs/flops before the last permutation\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MuxPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupWithMuxPos( Gia_Man_t * p );
    Gia_Man_t * pGia;
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
        Abc_Print( -1, "Abc_CommandAbc9MuxPos(): There is no AIG.\n" );
        return 1;
    }
    pGia = Gia_ManDupWithMuxPos( pAbc->pGia );
    Abc_FrameUpdateGia( pAbc, pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &muxpos [-vh]\n" );
    Abc_Print( -2, "\t         create additional POs to preserve MUXes\n" );
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
int Abc_CommandAbc9MuxStr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCofStructure( Gia_Man_t * p );
    Gia_Man_t * pGia;
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
        Abc_Print( -1, "Abc_CommandAbc9MuxStr(): There is no AIG.\n" );
        return 1;
    }
    pGia = Gia_ManCofStructure( pAbc->pGia );
    Abc_FrameUpdateGia( pAbc, pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &muxstr [-vh]\n" );
    Abc_Print( -2, "\t         performs restructuring\n" );
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
int Abc_CommandAbc9MuxDec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManPerformMuxDec( Gia_Man_t * p );
    Gia_Man_t * pGia;
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
        Abc_Print( -1, "Abc_CommandAbc9MuxDec(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManCiNum(pAbc->pGia) <= 6 || Gia_ManCiNum(pAbc->pGia) > 26 )
    {
        Abc_Print( -1, "Abc_CommandAbc9MuxDec(): The number of inputs is wrong.\n" );
        return 1;
    }
    pGia = Gia_ManPerformMuxDec( pAbc->pGia );
    Abc_FrameUpdateGia( pAbc, pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &muxdec [-vh]\n" );
    Abc_Print( -2, "\t         performs restructuring\n" );
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
int Abc_CommandAbc9Rex2Gia( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManRex2Gia( char * pStr, int fOrder, int fVerbose );
    Gia_Man_t * pGia = NULL;
    char * pStr = NULL;
    char ** pArgvNew;
    int nArgcNew;
    int c, fOrder = 1, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "avh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fOrder ^= 1;
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
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "No regular expression is entered on the command line.\n" );
        return 1;
    }
    pStr = pArgvNew[0];
    pGia = Gia_ManRex2Gia( pStr, fOrder, fVerbose );
    if ( pGia )
        Abc_FrameUpdateGia( pAbc, pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &rex2gia [-avh] [string]\n" );
    Abc_Print( -2, "\t         converts a regular expression into a sequential AIG\n" );
    Abc_Print( -2, "\t-a     : toggle ordering input symbols alphabetically [default = %s]\n", fOrder? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tstring : representation of a regular expression\n");
    Abc_Print( -2, "\t         Special symbols: parentheses \'(\' and \')\', Kleene closure \'*\', union \'|'\n");
    Abc_Print( -2, "\t         All other characters are treated as symbols of the input alphabet.\n");
    Abc_Print( -2, "\t         For example, ((A*B|AC)D) is defined over the alphabet {A, B, C, D}\n");
    Abc_Print( -2, "\t         and generates the following language: {BD, ABD, AABD, AAABD, ..., ACD}\n");
    Abc_Print( -2, "\t         A known limitation:  For the command to work correctly, each two-input union\n");
    Abc_Print( -2, "\t         should have a dedicated pair of parentheses: ((A|B)|C) rather than (A|B|C)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Strash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupMuxRestructure( Gia_Man_t * p );
    extern Gia_Man_t * Gia_ManDupUnhashMapping( Gia_Man_t * p );
    Gia_Man_t * pTemp;
    int c, Limit = 2;
    int Multi = 0;
    int fAddBuffs  = 0;
    int fAddStrash = 0;
    int fCollapse  = 0;
    int fAddMuxes  = 0;
    int fStrMuxes  = 0;
    int fRehashMap = 0;
    int fUnhashMap = 0;
    int fInvert    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LMbacmrusih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            Limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Limit < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            Multi = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Multi <= 0 )
                goto usage;
            break;
        case 'b':
            fAddBuffs ^= 1;
            break;
        case 'a':
            fAddStrash ^= 1;
            break;
        case 'c':
            fCollapse ^= 1;
            break;
        case 'm':
            fAddMuxes ^= 1;
            break;
        case 'r':
            fRehashMap ^= 1;
            break;
        case 'u':
            fUnhashMap ^= 1;
            break;
        case 's':
            fStrMuxes ^= 1;
            break;
        case 'i':
            fInvert ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Strash(): There is no AIG.\n" );
        return 1;
    }
    if ( fInvert )
    {
        Gia_Obj_t * pObj; int i;
        Gia_ManForEachPo( pAbc->pGia, pObj, i )
            Gia_ObjFlipFaninC0( pObj );
        return 0;        
    }
    if ( fAddBuffs )
    {
        extern Gia_Man_t * Gia_ManDupAddBufs( Gia_Man_t * p );
        pTemp = Gia_ManDupAddBufs( pAbc->pGia );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( Multi > 0 )
    {
        extern Gia_Man_t * Gia_ManDupAddPis( Gia_Man_t * p, int nMulti );
        pTemp = Gia_ManDupAddPis( pAbc->pGia, Multi );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( fStrMuxes )
    {
        if ( Gia_ManHasMapping(pAbc->pGia) )
            Abc_Print( 0, "Restructing the current AIG destroys the LUT mapping.\n" );
        Vec_IntFreeP( &pAbc->pGia->vMapping );
        pTemp = Gia_ManDupMuxRestructure( pAbc->pGia );
        Abc_Print( 1, "Finished AIG restructing to enable efficient mapping of 4:1 MUXes into 4-LUTs.\n" );
    }
    else if ( Gia_ManHasMapping(pAbc->pGia) && fRehashMap )
    {
        pTemp = Gia_ManDupHashMapping( pAbc->pGia );
        Gia_ManTransferPacking( pTemp, pAbc->pGia );
        Gia_ManTransferTiming( pTemp, pAbc->pGia );
    }
    else if ( Gia_ManHasMapping(pAbc->pGia) && fUnhashMap )
    {
        pTemp = Gia_ManDupUnhashMapping( pAbc->pGia );
        Gia_ManTransferPacking( pTemp, pAbc->pGia );
        Gia_ManTransferTiming( pTemp, pAbc->pGia );
    }
    else if ( Gia_ManHasMapping(pAbc->pGia) && pAbc->pGia->vConfigs2 )
        pTemp = (Gia_Man_t *)If_ManDeriveGiaFromCells2( pAbc->pGia );
    else if ( Gia_ManHasMapping(pAbc->pGia) && pAbc->pGia->vConfigs )
        pTemp = (Gia_Man_t *)If_ManDeriveGiaFromCells( pAbc->pGia );
    else if ( Gia_ManHasMapping(pAbc->pGia) )
        pTemp = (Gia_Man_t *)Dsm_ManDeriveGia( pAbc->pGia, fAddMuxes ); // delay-oriented unmapping
    else if ( fAddMuxes )
    {
        if ( pAbc->pGia->pMuxes )
        {
            Abc_Print( -1, "Abc_CommandAbc9Strash(): The AIG already has MUXes.\n" );
            return 1;
        }
        pTemp = Gia_ManDupMuxes( pAbc->pGia, Limit );
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "Generated AND/XOR/MUX graph.\n" );
    }
    else if ( fCollapse && pAbc->pGia->pAigExtra )
    {
        assert( !Gia_ManBufNum(pAbc->pGia) );
        if ( Gia_ManIsSeqWithBoxes(pAbc->pGia) || Gia_ManRegBoxNum(pAbc->pGia) )
        {
            Gia_Man_t * pUnshuffled = Gia_ManDupUnshuffleInputs( pAbc->pGia );
            Gia_ManTransferTiming( pUnshuffled, pAbc->pGia );
            pTemp = Gia_ManDupCollapse( pUnshuffled, pUnshuffled->pAigExtra, NULL, Gia_ManRegBoxNum(pUnshuffled) > 0 );
            Gia_ManTransferTiming( pAbc->pGia, pUnshuffled );
            Gia_ManStop( pUnshuffled );
        }
        else
            pTemp = Gia_ManDupCollapse( pAbc->pGia, pAbc->pGia->pAigExtra, NULL, 0 );
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "Collapsed AIG with boxes and logic of the boxes.\n" );
    }
    else if ( pAbc->pGia->pMuxes )
    {
        pTemp = Gia_ManDupNoMuxes( pAbc->pGia, 0 );
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "Generated AIG from AND/XOR/MUX graph.\n" );
    }
    else
    {
        pTemp = Gia_ManRehash( pAbc->pGia, fAddStrash );
//        if ( !Abc_FrameReadFlag("silentmode") )
//            printf( "Rehashed the current AIG.\n" );
    }
    if ( !(fCollapse && pAbc->pGia->pAigExtra) )
    {
        Gia_ManTransferTiming( pTemp, pAbc->pGia );
        pAbc->pGia->vConfigs = pTemp->vConfigs;     pTemp->vConfigs = NULL;
        pAbc->pGia->pCellStr = pTemp->pCellStr;     pTemp->pCellStr = NULL;
        pAbc->pGia->vConfigs2= pTemp->vConfigs2;    pTemp->vConfigs2= NULL;
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &st [-LM num] [-bacmrusih]\n" );
    Abc_Print( -2, "\t         performs structural hashing\n" );
    Abc_Print( -2, "\t-b     : toggle adding buffers at the inputs and outputs [default = %s]\n", fAddBuffs? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle additional hashing [default = %s]\n", fAddStrash? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle collapsing hierarchical AIG [default = %s]\n", fCollapse? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle converting to larger gates [default = %s]\n", fAddMuxes? "yes": "no" );
    Abc_Print( -2, "\t-L num : create MUX when sum of refs does not exceed this limit [default = %d]\n", Limit );
    Abc_Print( -2, "\t         (use L = 1 to create AIG with XORs but without MUXes)\n" );
    Abc_Print( -2, "\t-M num : create an AIG with additional primary inputs [default = %d]\n", Multi );
    Abc_Print( -2, "\t-r     : toggle rehashing AIG while preserving mapping [default = %s]\n", fRehashMap? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle unhashing AIG while preserving mapping [default = %s]\n", fUnhashMap? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using MUX restructuring [default = %s]\n", fStrMuxes? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle complementing the POs of the AIG [default = %s]\n", fInvert? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Topand( Abc_Frame_t * pAbc, int argc, char ** argv )
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
        Abc_Print( -1, "Abc_CommandAbc9Topand(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Topand(): Can only be applied to a combinational miter.\n" );
        return 1;
    }
    pTemp = Gia_ManDupTopAnd( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &topand [-vh]\n" );
    Abc_Print( -2, "\t        performs AND decomposition for combinational miter\n" );
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
int Abc_CommandAbc9Cof( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManComputeCofs( Gia_Man_t * p, int nVars );
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int iVar = 0, Const = -1, nLimFan = 0, nVars = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "VCLNvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            Const = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Const < 0 || Const > 1 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLimFan = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimFan < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Cof(): There is no AIG.\n" );
        return 1;
    }
    if ( Const == 0 || Const == 1 )
    {
        Abc_Print( 0, "Computing cofactor of var %d with value %d.\n", iVar, Const );
        pTemp = Gia_ManDupCofactorVar( pAbc->pGia, iVar, Const );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    else if ( nVars )
    {
        Abc_Print( 0, "Cofactoring the last %d inputs.\n", nVars );
        pTemp = Gia_ManComputeCofs( pAbc->pGia, nVars );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    else if ( nLimFan )
    {
        Abc_Print( 0, "Cofactoring all variables whose fanout count is higher than %d.\n", nLimFan );
        pTemp = Gia_ManDupCofAll( pAbc->pGia, nLimFan, fVerbose );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    else if ( iVar )
    {
        Abc_Print( 0, "Cofactoring one variable with object ID %d.\n", iVar );
        pTemp = Gia_ManDupCof( pAbc->pGia, iVar );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    else
    {
        Abc_Print( -1, "One of the parameters, -V <num> or -L <num>, should be set on the command line.\n" );
        goto usage;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &cof [-VCLN num] [-vh]\n" );
    Abc_Print( -2, "\t         performs cofactoring w.r.t. variable(s)\n" );
    Abc_Print( -2, "\t-V num : the zero-based ID of one variable to cofactor [default = %d]\n", iVar );
    Abc_Print( -2, "\t-C num : cofactor one variable with a given constant (0 or 1) [default = unused]\n" );
    Abc_Print( -2, "\t-L num : cofactor vars with fanout count higher than this [default = %d]\n", nLimFan );
    Abc_Print( -2, "\t-N num : cofactoring the given number of last input variables [default = %d]\n", nVars );
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
int Abc_CommandAbc9Cofs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupCofs( Gia_Man_t * p, Vec_Int_t * vVarNums );
    extern Gia_Man_t * Gia_ManDupUnCofs( Gia_Man_t * p, Vec_Int_t * vVarNums );
    Gia_Man_t * pTemp;  Vec_Int_t * vVars = NULL;
    int c, iVar = 0, nVars = 0, fLastVars = 0, fVerbose = 0, fUndo = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "VNluvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
        case 'l':
            fLastVars ^= 1;
            break;
        case 'u':
            fUndo ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Cof(): There is no AIG.\n" );
        return 1;
    }
    if ( iVar ) {
        Abc_Print( 0, "Cofactoring one variable with ID %d.\n", iVar );
        vVars = Vec_IntAlloc( 1 );
        Vec_IntPush( vVars, iVar );
    }
    else if ( nVars ) {
        Abc_Print( 0, "Cofactoring the %s %d inputs.\n", fLastVars ? "last":"first", nVars );
        if ( fLastVars) {
            vVars = Vec_IntAlloc(nVars);
            for ( int v = 0; v < nVars; v++ )
                Vec_IntPush( vVars, Gia_ManCiNum(pAbc->pGia)-nVars+v );
        }
        else
            vVars = Vec_IntStartNatural( nVars );
    }
    else if ( globalUtilOptind < argc ) {
        vVars = Vec_IntAlloc( argc );
        for ( c = globalUtilOptind; c < argc; c++ )
            Vec_IntPush( vVars, atoi(argv[c]) );
    }
    else {
        Abc_Print( -1, "One of the parameters, -V <num> or -L <num>, should be set on the command line.\n" );
        goto usage;
    }
    pTemp = fUndo ? Gia_ManDupUnCofs( pAbc->pGia, vVars ) : Gia_ManDupCofs( pAbc->pGia, vVars );
    Abc_FrameUpdateGia( pAbc, pTemp );
    Vec_IntFree( vVars );
    return 0;

usage:
    Abc_Print( -2, "usage: &cofs [-VN num] [-luvh]\n" );
    Abc_Print( -2, "\t         derives cofactors or reconstructs them w.r.t the set of variables\n" );
    Abc_Print( -2, "\t-V num : the zero-based ID of one variable to cofactor [default = %d]\n", iVar );
    Abc_Print( -2, "\t-N num : cofactoring the given number of first input variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-l     : toggle cofactoring last variables instead [default = %s]\n", fLastVars? "yes": "no" );
    Abc_Print( -2, "\t-u     : undo cofactoring (recombine cofactors using muxes) [default = %s]\n", fUndo? "yes": "no" );
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
int Abc_CommandAbc9Trim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp, * pTemp2;
    int c;
    int OutValue = -1;
    int fTrimCis = 1;
    int fTrimCos = 1;
    int fDualOut = 0;
    int fPoFedByPi = 0;
    int fPoFedByPo = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Viocpdh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            OutValue = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( OutValue < 0 )
                goto usage;
            break;
        case 'i':
            fTrimCis ^= 1;
            break;
        case 'o':
            fTrimCos ^= 1;
            break;
        case 'c':
            fPoFedByPi ^= 1;
            break;
        case 'p':
            fPoFedByPo ^= 1;
            break;
        case 'd':
            fDualOut ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Trim(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManDupTrimmed( pAbc->pGia, fTrimCis, fTrimCos, fDualOut, OutValue );
    if ( fPoFedByPi )
    {
        extern Gia_Man_t * Gia_ManDupTrimmed2( Gia_Man_t * p );
        pTemp = Gia_ManDupTrimmed2( pTemp2 = pTemp );
        Gia_ManStop( pTemp2 );
    }
    if ( fPoFedByPo )
    {
        extern Gia_Man_t * Gia_ManDupTrimmed3( Gia_Man_t * p );
        pTemp = Gia_ManDupTrimmed3( pTemp2 = pTemp );
        Gia_ManStop( pTemp2 );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &trim [-V num] [-iocpdh]\n" );
    Abc_Print( -2, "\t         removes PIs without fanout and PO driven by constants\n" );
    Abc_Print( -2, "\t-V num : the value (0 or 1) of POs to remove [default = both]\n" );
    Abc_Print( -2, "\t-i     : toggle removing PIs [default = %s]\n", fTrimCis? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle removing POs [default = %s]\n", fTrimCos? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle additionally removing POs fed by PIs [default = %s]\n", fPoFedByPi? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle additionally removing duplicated POs [default = %s]\n", fPoFedByPo? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle using dual-output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupChoices( Gia_Man_t * p );
    Gia_Man_t * pTemp;
    int c;
    int fNormal  = 0;
    int fChoices = 0;
    int fRevFans = 0;
    int fRevOuts = 0;
    int fLeveled = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ncfolvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fNormal ^= 1;
            break;
        case 'c':
            fChoices ^= 1;
            break;
        case 'f':
            fRevFans ^= 1;
            break;
        case 'o':
            fRevOuts ^= 1;
            break;
        case 'l':
            fLeveled ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Dfs(): There is no AIG.\n" );
        return 1;
    }
    if ( fChoices )
        pTemp = pAbc->pGia->pSibls ? Gia_ManDupChoices(pAbc->pGia) : Gia_ManDup(pAbc->pGia);
    else if ( fLeveled )
        pTemp = Gia_ManDupLevelized( pAbc->pGia );
    else if ( fNormal )
        pTemp = Gia_ManDupOrderAiger( pAbc->pGia );
    else 
        pTemp = Gia_ManDupOrderDfsReverse( pAbc->pGia, fRevFans, fRevOuts );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dfs [-ncfolvh]\n" );
    Abc_Print( -2, "\t        orders objects in the DFS order\n" );
    Abc_Print( -2, "\t-n    : toggle using normalized ordering [default = %s]\n",            fNormal? "yes": "no" );
    Abc_Print( -2, "\t-c    : toggle using ordering for AIG with choices [default = %s]\n",  fChoices? "yes": "no" );
    Abc_Print( -2, "\t-f    : toggle using reverse fanin traversal order [default = %s]\n",  fRevFans? "yes": "no" );
    Abc_Print( -2, "\t-o    : toggle using reverse output traversal order [default = %s]\n", fRevOuts? "yes": "no" );
    Abc_Print( -2, "\t-l    : toggle using levelized order [default = %s]\n",                fLeveled? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n",         fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Times( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, nTimes = 2, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimes < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Times(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManDupTimes( pAbc->pGia, nTimes );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &times [-N <num>] [-vh]\n" );
    Abc_Print( -2, "\t         creates several \"parallel\" copies of the design\n" );
    Abc_Print( -2, "\t-N num : number of copies to create [default = %d]\n", nTimes );
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
int Abc_CommandAbc9Append( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Gia_Man_t * pSecond;
    char * FileName, * pTemp;
    char ** pArgvNew;
    int nArgcNew;
    int c, fShareCis = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fShareCis ^= 1;
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
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }

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
    pSecond = Gia_AigerRead( FileName, 0, 0, 0 );
    if ( pSecond == NULL )
    {
        Abc_Print( -1, "Reading AIGER has failed.\n" );
        return 0;
    }
    if ( fShareCis && Gia_ManCiNum(pAbc->pGia) != Gia_ManCiNum(pSecond) )
    {
        Abc_Print( -1, "The AIGs have different number of combinational inputs.\n" );
        return 0;
    }
    // compute the miter
    Gia_ManDupAppend( pAbc->pGia, pSecond, fShareCis );
    Gia_ManStop( pSecond );
    return 0;

usage:
    Abc_Print( -2, "usage: &append [-ivh] <file>\n" );
    Abc_Print( -2, "\t         appends <file> to the current AIG using new PIs and POs\n" );
    Abc_Print( -2, "\t-i     : toggle sharing combinational inputs [default = %s]\n", fShareCis? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : AIGER file with the design to miter\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Posplit( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Aig_Man_t * Aig_ManSplit( Aig_Man_t * p, int nVars, int fVerbose );
    Aig_Man_t * pMan, * pAux;
    Gia_Man_t * pTemp = NULL;
    int c, nVars = 5, fVerbose = 0;
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
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Posplit(): There is no AIG.\n" );
        return 1;
    }
    pMan = Gia_ManToAigSimple( pAbc->pGia );
    pMan = Aig_ManSplit( pAux = pMan, nVars, fVerbose );
    Aig_ManStop( pAux );
    if ( pMan != NULL )
    {
        pTemp = Gia_ManFromAigSimple( pMan );
        Aig_ManStop( pMan );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &posplit [-N num] [-vh]\n" );
    Abc_Print( -2, "\t         cofactors the property output w.r.t. a support subset\n" );
    Abc_Print( -2, "\t         (the OR of new PO functions is equal to the original property)\n" );
    Abc_Print( -2, "\t-N num : the number of random cofactoring variables [default = %d]\n", nVars );
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
int Abc_CommandAbc9Permute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupRandPerm( Gia_Man_t * p, int fVerbose );
    Gia_Man_t * pTemp;
    int c, RandSeed = 0, fVerbose = 0;
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
            RandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( RandSeed < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Permute(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Permute(): This command does not work for sequential AIGs.\n" );
        return 1;
    }
    Abc_Random(1);
    for ( c = 0; c < RandSeed; c++ )
        Abc_Random(0);
    pTemp = Gia_ManDupRandPerm( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &permute [-S num] [-vh]\n" );
    Abc_Print( -2, "\t         generates a random NPNP transformation of the combinational AIG\n" );
    Abc_Print( -2, "\t-S num : the seed used to randomize the process [default = %d]\n", RandSeed );
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
int Abc_CommandAbc9Cone( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    Vec_Int_t * vPos;
    int c, nRegs = 0, iOutNum = -1, nOutRange = 1, iPartNum = -1, iConeNum = -1, nLevelMax = 0, nTimeWindow = 0, fUseAllCis = 0, fExtractAll = 0, fComb = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ORPLWCaecvh" ) ) != EOF )
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
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            iPartNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iPartNum < 0 )
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
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeWindow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeWindow < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            iConeNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iConeNum < 1 )
                goto usage;
            break;
        case 'a':
            fUseAllCis ^= 1;
            break;
        case 'e':
            fExtractAll ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Cone(): There is no AIG.\n" );
        return 1;
    }
    if ( fExtractAll )
    {
        char Buffer[1000];
        Gia_Obj_t * pObj; int i;
        unsigned char nDigits = (unsigned char)Abc_Base10Log(Gia_ManPoNum(pAbc->pGia));
        Gia_ManForEachPo( pAbc->pGia, pObj, i )
        {
            Gia_Man_t * pOne = Gia_ManDupDfsCone( pAbc->pGia, pObj );
            sprintf( Buffer, "%s_%0*d.aig", Extra_FileNameGeneric(pAbc->pGia->pSpec), nDigits, i );
            Gia_AigerWrite( pOne, Buffer, 0, 0, 0 );
            Gia_ManStop( pOne );
        }
        printf( "Dumped all outputs into individual AIGER files.\n" );
        return 0;
    }
    if ( nLevelMax || nTimeWindow )
    {
        if ( nLevelMax && nTimeWindow )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cone(): Parameters -L (max level) and -W (timing window) cannot be specified at the same time.\n" );
            return 1;
        }
        else
        {
            pTemp = Gia_ManExtractWindow( pAbc->pGia, nLevelMax, nTimeWindow, fVerbose );
            Abc_FrameUpdateGia( pAbc, pTemp );
            return 0;
        }
    }
    if ( iConeNum > 0 )
    {
        if ( iConeNum >= Gia_ManObjNum(pAbc->pGia) || !Gia_ObjIsAnd(Gia_ManObj(pAbc->pGia, iConeNum)) ) 
        {
            Abc_Print( -1, "Abc_CommandAbc9Cone(): Object with Id %d is not a node.\n", iConeNum );
            return 1;
        }
        pTemp = Gia_ManDupDfsNode( pAbc->pGia, Gia_ManObj(pAbc->pGia, iConeNum) );
        Abc_FrameUpdateGia( pAbc, pTemp );    
        return 0;    
    }
    if ( iPartNum >= 0 )
    {
        Vec_Int_t * vClass;
        Vec_Vec_t * vClasses = (Vec_Vec_t *)pAbc->vPoEquivs;
        if ( vClasses == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cone(): Partitions are not defined.\n" );
            return 1;
        }
        if ( iPartNum >= Vec_VecSize(vClasses) )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cone(): Partition index exceed the array size.\n" );
            return 1;
        }
        vClass = Vec_VecEntryInt( vClasses, iPartNum );
        pTemp = Gia_ManDupCones( pAbc->pGia, Vec_IntArray(vClass), Vec_IntSize(vClass), !fUseAllCis );
        if ( pTemp )
            Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    nRegs = Gia_ManRegNum( pAbc->pGia );
    if ( fComb )
        pAbc->pGia->nRegs = 0;
    if ( iOutNum < 0 || iOutNum + nOutRange > Gia_ManPoNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Cone(): Range of outputs to extract is incorrect.\n" );
        if ( fComb )
            Gia_ManSetRegNum( pAbc->pGia, nRegs );
        return 1;
    }
    vPos = Vec_IntStartRange( iOutNum, nOutRange );
    pTemp = Gia_ManDupCones( pAbc->pGia, Vec_IntArray(vPos), nOutRange, !fUseAllCis );
    if ( fComb )
        Gia_ManSetRegNum( pAbc->pGia, nRegs );
    Vec_IntFree( vPos );
    if ( pTemp )
        Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &cone [-ORPLWC num] [-aecvh]\n" );
    Abc_Print( -2, "\t         extracting multi-output sequential logic cones\n" );
    Abc_Print( -2, "\t-O num : the index of first PO to extract [default = %d]\n", iOutNum );
    Abc_Print( -2, "\t-R num : (optional) the number of outputs to extract [default = %d]\n", nOutRange );
    Abc_Print( -2, "\t-P num : (optional) the partition number to extract [default = %d]\n", iPartNum );
    Abc_Print( -2, "\t-L num : (optional) extract cones with higher level [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-W num : (optional) extract cones falling into this window [default = %d]\n", nTimeWindow );
    Abc_Print( -2, "\t-C num : (optional) extract cone of one node with ID equal to <num> [default = unused]\n" );
    Abc_Print( -2, "\t-a     : toggle keeping all CIs or structral support only [default = %s]\n", fUseAllCis? "all": "structural" );
    Abc_Print( -2, "\t-e     : toggle writing all outputs into individual files [default = %s]\n", fExtractAll? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle performing cone extraction combinationally [default = %s]\n", fComb? "yes": "no" );
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
int Abc_CommandAbc9Slice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, nSuppSize = 6, fVerbose = 0;
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
            nSuppSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSuppSize < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9Slice(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManDupSliced( pAbc->pGia, nSuppSize );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &slice [-S num] [-vh]\n" );
    Abc_Print( -2, "\t         cuts the lower part of the AIG with nodes using their support\n" );
    Abc_Print( -2, "\t-S num : the largest support size to keep in the slide [default = %d]\n", nSuppSize );
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
int Abc_CommandAbc9PoPart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManFindPoPartition( Gia_Man_t * p, int SelectShift, int fOnlyCis, int fSetLargest, int fVerbose, Vec_Ptr_t ** pvPosEquivs );
    Gia_Man_t * pTemp;
    Vec_Ptr_t * vPosEquivs = NULL;
    int c, SelectShift = 0, fOnlyCis = 0, fSetLargest = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Simvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            SelectShift = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( SelectShift < 0 )
                goto usage;
            break;
        case 'i':
            fOnlyCis ^= 1;
            break;
        case 'm':
            fSetLargest ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9PoPart(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManFindPoPartition( pAbc->pGia, SelectShift, fOnlyCis, fSetLargest, fVerbose, &vPosEquivs );
    if ( pTemp )
        Abc_FrameUpdateGia( pAbc, pTemp );
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );
    return 0;

usage:
    Abc_Print( -2, "usage: &popart [-S num] [-imvh]\n" );
    Abc_Print( -2, "\t         partitioning of POs into equivalence classes\n" );
    Abc_Print( -2, "\t-S num : random seed to select the set of pivot nodes [default = %d]\n", SelectShift );
    Abc_Print( -2, "\t       : (if the seed is 0, the nodes with max fanout counts are used)\n" );
    Abc_Print( -2, "\t-i     : toggle allowing only CIs to be the pivots [default = %s]\n", fOnlyCis? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using the largest part as the current network [default = %s]\n", fSetLargest? "yes": "no" );
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
int Abc_CommandAbc9PoPart2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManFindPoPartition2( Gia_Man_t * p, int iStartNum, int nDelta, int nOutsMin, int nOutsMax, int fSetLargest, int fVerbose, Vec_Ptr_t ** pvPosEquivs );
    Gia_Man_t * pTemp = NULL;
    Vec_Ptr_t * vPosEquivs = NULL;
    int c, iStartNum = 0, nDelta = 10, nOutsMin = 100, nOutsMax = 1000, fSetLargest = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SDLUmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            iStartNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iStartNum < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDelta < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nOutsMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOutsMin < 0 )
                goto usage;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by an integer.\n" );
                goto usage;
            }
            nOutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOutsMax < 0 )
                goto usage;
            break;
        case 'm':
            fSetLargest ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9PoPart(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManFindPoPartition2( pAbc->pGia, iStartNum, nDelta, nOutsMin, nOutsMax, fSetLargest, fVerbose, &vPosEquivs );
    if ( pTemp )
        Abc_FrameUpdateGia( pAbc, pTemp );
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );
    return 0;

usage:
    Abc_Print( -2, "usage: &popart2 [-SDLU num] [-mvh]\n" );
    Abc_Print( -2, "\t         extracting multi-output sequential logic cones\n" );
    Abc_Print( -2, "\t-S num : the index of the PO to start the cluster [default = %d]\n", iStartNum );
    Abc_Print( -2, "\t-D num : the max increase in flop count after adding one PO [default = %d]\n", nDelta );
    Abc_Print( -2, "\t-L num : the minimum number of POs in a cluster [default = %d]\n", nOutsMin );
    Abc_Print( -2, "\t-U num : the maximum number of POs in a cluster [default = %d]\n", nOutsMax );
    Abc_Print( -2, "\t-m     : toggle selecting the largest cluster [default = %s]\n", fSetLargest? "yes": "no" );
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
int Abc_CommandAbc9PutOnTop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_GenPutOnTop( char ** pFNames, int nFNames );
    Gia_Man_t * pMan = NULL;
    int c, fVerbose = 0;
    char ** pArgvNew;
    int     nArgcNew;
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
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;    
    if ( nArgcNew < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9PutOnTop(): At least one AIG file should be given on the command line.\n" );
        return 0;
    }        
    pMan = Gia_GenPutOnTop( pArgvNew, nArgcNew );
    if ( pMan == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PutOnTop(): Computing the resulting AIS has failed.\n" );
        return 0;
    }    
    Abc_FrameUpdateGia( pAbc, pMan );
    return 0;
usage:
    Abc_Print( -2, "usage: &putontop [-vh] <file[1]> <file[2]> ...  <file[N]>\n" );
    Abc_Print( -2, "\t            generates an AIG by stacking several AIGs on top of each other\n" );
    Abc_Print( -2, "\t-v        : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h        : print the command usage\n");
    Abc_Print( -2, "\t<files>   : the AIGER files containing the input AIGs\n");
    Abc_Print( -2, "\t            the outputs of each AIG are connected to the inputs of the one on top of it\n" );
    Abc_Print( -2, "\t            if there are more outputs than inputs, new POs will be created\n" );
    Abc_Print( -2, "\t            if there are more inputs than outputs, new PIs are created\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Window( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupWindow( Gia_Man_t * p, Vec_Int_t * vCut );
    Gia_Man_t * pNew = NULL;
    Vec_Int_t * vCut = NULL;
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
        Abc_Print( -1, "Abc_CommandAbc9Window(): There is no AIG.\n" );
        return 0;
    }
    if ( argc == globalUtilOptind )
    {
        int nCutSize = 6, nCuts = 30;
        extern void Gia_ManExploreCutsTest( Gia_Man_t * pGia, int nCutSize, int nCuts, int fVerbose );
        printf( "Here are %d the most frequently appearing %d-cuts:\n", nCutSize, nCuts );
        Gia_ManExploreCutsTest( pAbc->pGia, nCutSize, nCuts, fVerbose );
        return 0;
    }
    if ( argc-globalUtilOptind < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Window(): The window should have at least one support variable.\n" );
        return 0;
    }
    vCut = Vec_IntAlloc( 100 );
    for ( c = globalUtilOptind; c < argc; c++ )
        Vec_IntPush( vCut, atoi(argv[c]) );    
    pNew = Gia_ManDupWindow( pAbc->pGia, vCut );
    Abc_FrameUpdateGia( pAbc, pNew );
    Vec_IntFree( vCut );
    return 0;

usage:
    Abc_Print( -2, "usage: &window [-vh] <node1> <node2> ... <nodeN>\n" );
    Abc_Print( -2, "\t          generates a logic window supported by the given nodes\n" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<nodes> : the list of window inputs\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AndCare( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupAndCare( Gia_Man_t * p, Gia_Man_t * pCare );
    Gia_Man_t * pTemp = NULL, * pCare = NULL; int c, fVerbose = 0;
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
        Abc_Print( -1, "Abc_CommandAbc9AndCare(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 1,"Abc_CommandAbc9AndCare(): There is no careset AIG.\n" );
        return 0;
    }
    pCare = Gia_AigerRead( argv[globalUtilOptind], 0, 0, 0 );
    if ( pCare == NULL )
        Abc_Print( -1, "Abc_CommandAbc9AndCare(): Reading careset from file has failed.\n" );
    else if ( Gia_ManPiNum(pAbc->pGia) != Gia_ManPiNum(pCare) )
        Abc_Print( -1, "Abc_CommandAbc9AndCare(): Careset should have the same number of primary inputs.\n" );
    else {
        pTemp = Gia_ManDupAndCare( pAbc->pGia, pCare );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    Gia_ManStop( pCare );
    return 0;

usage:
    Abc_Print( -2, "usage: &andcare [-vh] <file>\n" );
    Abc_Print( -2, "\t          computes the conjunction of each primary output with the careset\n" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<file>  : input AIG file with the careset\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Divide( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManDupSplit( Gia_Man_t * p, int nParts, int nCutLevel );
    int nParts = 2;
    int nCutLevel = 0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PLvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nParts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nParts < 2 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutLevel < 0 )
                goto usage;
            break;
        case 'v':
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Divide(): There is no AIG.\n" );
        return 0;
    }
    Gia_ManDupSplit( pAbc->pGia, nParts, nCutLevel );
    return 0;

usage:
    Abc_Print( -2, "usage: &divide [-P num] [-L num] [-vh]\n" );
    Abc_Print( -2, "\t         divides AIG into N parts at different levels\n" );
    Abc_Print( -2, "\t-P num : number of parts to divide into [default = %d]\n", nParts );
    Abc_Print( -2, "\t-L num : cut level (0 = automatic middle level) [default = %d]\n", nCutLevel );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = no]\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
