/**CFile****************************************************************

  FileName    [abcAbstract.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Verification abstraction and constraints.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "proof/abs/abs.h"
#include "bdd/llb/llb.h"
#include "aig/saig/saig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandExtSeqDcs              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEnlarge                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTempor                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandConstr                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnfold                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFold                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnfold2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFold2                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
#ifdef ABC_USE_CUDD
static int Abc_CommandReconcile              ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
static int Abc_CommandDualRail               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBlockPo                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Uif                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenQbf             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsCreate          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsDerive          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsRefine          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaDerive          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaRefine          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaShrink          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Gla                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Vta                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Vta2Gla            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Gla2Vta            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Fla2Gla            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Gla2Fla            ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandAbcLivenessToSafety    ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandAbcLivenessToSafetySim ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandAbcLivenessToSafetyWithLTL( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandCS_kLiveness           ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );

/**Function*************************************************************

  Synopsis    [Registers verification abstraction and constraints commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitAbstract( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Various",      "ext_seq_dcs",   Abc_CommandExtSeqDcs,        0 );
    Cmd_CommandAdd( pAbc, "Verification", "enlarge",       Abc_CommandEnlarge,          1 );
    Cmd_CommandAdd( pAbc, "Verification", "tempor",        Abc_CommandTempor,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "constr",        Abc_CommandConstr,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "unfold",        Abc_CommandUnfold,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "fold",          Abc_CommandFold,             1 );
    Cmd_CommandAdd( pAbc, "Verification", "unfold2",       Abc_CommandUnfold2,          1 );    // jlong
    Cmd_CommandAdd( pAbc, "Verification", "fold2",         Abc_CommandFold2,            1 );    // jlong
#ifdef ABC_USE_CUDD
    Cmd_CommandAdd( pAbc, "Verification", "reconcile",     Abc_CommandReconcile,        1 );
#endif
    Cmd_CommandAdd( pAbc, "Verification", "dualrail",      Abc_CommandDualRail,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "blockpo",       Abc_CommandBlockPo,          1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&uif",          Abc_CommandAbc9Uif,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&genqbf",       Abc_CommandAbc9GenQbf,       0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&abs_create",   Abc_CommandAbc9AbsCreate,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&abs_derive",   Abc_CommandAbc9AbsDerive,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&abs_refine",   Abc_CommandAbc9AbsRefine,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla_derive",   Abc_CommandAbc9GlaDerive,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla_refine",   Abc_CommandAbc9GlaRefine,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla_shrink",   Abc_CommandAbc9GlaShrink,    0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla",          Abc_CommandAbc9Gla,          0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&vta",          Abc_CommandAbc9Vta,          0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&vta_gla",      Abc_CommandAbc9Vta2Gla,      0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla_vta",      Abc_CommandAbc9Gla2Vta,      0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&fla_gla",      Abc_CommandAbc9Fla2Gla,      0 );
    Cmd_CommandAdd( pAbc, "Abstraction",  "&gla_fla",      Abc_CommandAbc9Gla2Fla,      0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "l2s",           Abc_CommandAbcLivenessToSafety,        0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "l2ssim",        Abc_CommandAbcLivenessToSafetySim,     0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "l3s",           Abc_CommandAbcLivenessToSafetyWithLTL, 0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "kcs",           Abc_CommandCS_kLiveness,               0 );
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
int Abc_CommandExtSeqDcs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern int Abc_NtkExtractSequentialDcs( Abc_Ntk_t * pNet, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
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
        Abc_Print( -1, "Extracting sequential don't-cares works only for AIGs (run \"strash\").\n" );
        return 0;
    }
    if ( !Abc_NtkExtractSequentialDcs( pNtk, fVerbose ) )
    {
        Abc_Print( -1, "Extracting sequential don't-cares has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: ext_seq_dcs [-vh]\n" );
    Abc_Print( -2, "\t         create EXDC network using unreachable states\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEnlarge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nFrames;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarEnlarge( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames      = 5;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
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
            if ( nFrames < 1 )
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

    // modify the current network
    pNtkRes = Abc_NtkDarEnlarge( pNtk, nFrames, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Target enlargement has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: enlarge [-F <num>] [-vh]\n" );
    Abc_Print( -2, "\t           performs structural K-step target enlargement\n" );
    Abc_Print( -2, "\t-F <num> : the number of timeframes to unroll (<num> > 0) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTempor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Cex_t * Abc_NtkDarTemporCex( Abc_Ntk_t * pNtk, Abc_Cex_t * pCex );
    extern Abc_Ntk_t * Abc_NtkDarTempor( Abc_Ntk_t * pNtk, int nFrames, int TimeOut, int nConfLimit, int fUseBmc, int fUseTransSigs, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    int nFrames       =       0;
    int TimeOut       =     300;
    int nConfMax      =  100000;
    int fUseBmc       =       1;
    int fUseTransSigs =       0;
    int fUpdateCex    =       0;
    int fVerbose      =       0;
    int fVeryVerbose  =       0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTCbscvwh" ) ) != EOF )
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
        case 'b':
            fUseBmc ^= 1;
            break;
        case 's':
            fUseTransSigs ^= 1;
            break;
        case 'c':
            fUpdateCex ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
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
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( 0, "The current network is combinational.\n");
        return 0;
    }
    if ( Abc_NtkPiNum(pNtk) == 0 )
    {
        Abc_Print( 0, "The current network does not have primary inputs. Use \"addpi\".\n");
        return 0;
    }
    if ( fUpdateCex )
    {
        Abc_Cex_t * pCexNew;
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( -1, "Counter-example is not available.\n" );
            return 1;
        }
        pCexNew = Abc_NtkDarTemporCex( pNtk, pAbc->pCex );
        if ( pCexNew == NULL )
        {
            Abc_Print( -1, "The counter-example does not match this network after temporal decomposition.\n" );
            return 1;
        }
        Abc_FrameReplaceCex( pAbc, &pCexNew );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarTempor( pNtk, nFrames, TimeOut, nConfMax, fUseBmc, fUseTransSigs, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Temporal decomposition has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: tempor [-FTC <num>] [-bscvwh]\n" );
    Abc_Print( -2, "\t           performs temporal decomposition\n" );
    Abc_Print( -2, "\t-F <num> : init logic timeframe count (0 = use leading length) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-T <num> : runtime limit in seconds for BMC (0=unused) [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-C <num> : max number of SAT conflicts in BMC (0=unused) [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-b       : toggle running BMC2 on the init frames [default = %s]\n", fUseBmc? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle using transient signals [default = %s]\n", fUseTransSigs? "yes": "no" );
    Abc_Print( -2, "\t-c       : update the current CEX derived for a new AIG after \"tempor\"\n" );
    Abc_Print( -2, "\t           to match the current AIG (the one before \"tempor\") [default = %s]\n", fUpdateCex? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing ternary state space [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandConstr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    Abc_Ntk_t * pNtkRes;
    int c;
    int nFrames;
    int nConfs;
    int nProps;
    int fRemove;
    int fPurge;
    int fStruct;
    int fInvert;
    int fOldAlgo;
    int fVerbose;
    int nConstrs;
    extern void Abc_NtkDarConstr( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkMakeOnePo( Abc_Ntk_t * pNtk, int Output, int nRange );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames   =      1;
    nConfs    =   1000;
    nProps    =   1000;
    fRemove   =      0;
    fPurge    =      0;
    fStruct   =      0;
    fInvert   =      0;
    fOldAlgo  =      0;
    fVerbose  =      0;
    nConstrs  =     -1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPNrpsiavh" ) ) != EOF )
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
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProps < 0 )
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
        case 'r':
            fRemove ^= 1;
            break;
        case 'p':
            fPurge ^= 1;
            break;
        case 's':
            fStruct ^= 1;
            break;
        case 'i':
            fInvert ^= 1;
            break;
        case 'a':
            fOldAlgo ^= 1;
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
    if ( fRemove )
    {
        if ( Abc_NtkConstrNum(pNtk) == 0 )
        {
            Abc_Print( -1, "Constraints are not defined.\n" );
            return 0;
        }

        if ( fPurge )
        {
            Abc_Print( 1, "Constraints are removed.\n" );
            pNtkRes = Abc_NtkMakeOnePo( pNtk, 0, Abc_NtkPoNum(pNtk) - Abc_NtkConstrNum(pNtk) );
            if ( pNtkRes == NULL )
            {
                Abc_Print( 1,"Transformation has failed.\n" );
                return 1;
            }
            // replace the current network
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
            pNtk = Abc_FrameReadNtk(pAbc);
        }
        else
            Abc_Print( 1, "Constraints are converted to be primary outputs.\n" );
        pNtk->nConstrs = 0;
        return 0;
    }
    // consider the case of manual constraint definition
    if ( nConstrs >= 0 )
    {
        if ( Abc_NtkIsComb(pNtk) )
            Abc_Print( 0, "The network is combinational.\n" );
        if ( Abc_NtkConstrNum(pNtk) > 0 )
            Abc_Print( 0, "The network currently has %d constraints.\n", Abc_NtkConstrNum(pNtk) );
        if ( nConstrs >= Abc_NtkPoNum(pNtk) )
        {
            Abc_Print( -1, "The number of constraints specified (%d) should be less than POs (%d).\n", nConstrs, Abc_NtkPoNum(pNtk) );
            return 0;
        }
        Abc_Print( 1, "Setting the last %d POs as constraint outputs.\n", nConstrs );
        pNtk->nConstrs = nConstrs;
        return 0;
    }
    // consider the case of already defined constraints
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        extern void Abc_NtkDarConstrProfile( Abc_Ntk_t * pNtk, int fVerbose );
        if ( fInvert )
        {
            Abc_NtkInvertConstraints( pNtk );
            if ( Abc_NtkConstrNum(pNtk) == 1 )
                Abc_Print( 1, "The output of %d constraint is complemented.\n", Abc_NtkConstrNum(pNtk) );
            else
                Abc_Print( 1, "The outputs of %d constraints are complemented.\n", Abc_NtkConstrNum(pNtk) );
        }
        if ( fVerbose )
            Abc_NtkDarConstrProfile( pNtk, fVerbose );
        return 0;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    // detect constraints using functional/structural methods
    Abc_NtkDarConstr( pNtk, nFrames, nConfs, nProps, fStruct, fOldAlgo, fVerbose );
    return 0;
usage:
    Abc_Print( -2, "usage: constr [-FCPN num] [-rpisavh]\n" );
    Abc_Print( -2, "\t         a toolkit for constraint manipulation\n" );
    Abc_Print( -2, "\t         if constraints are absent, detect them functionally\n" );
    Abc_Print( -2, "\t         if constraints are present, profiles them using random simulation\n" );
    Abc_Print( -2, "\t         (constraints fail when any of them becomes 1 in any timeframe)\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes to consider [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts in SAT solving [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-P num : the max number of propagations in SAT solving [default = %d]\n", nProps );
    Abc_Print( -2, "\t-N num : manually set the last <num> POs to be constraints [default = %d]\n", nConstrs );
    Abc_Print( -2, "\t-r     : manually remove the constraints, converting them to POs [default = %s]\n", fRemove? "yes": "no" );
    Abc_Print( -2, "\t-p     : remove constraints instead of converting them to POs [default = %s]\n", fPurge? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle inverting already defined constraints [default = %s]\n", fInvert? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using structural detection methods [default = %s]\n", fStruct? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle fast implication detection [default = %s]\n", !fOldAlgo? "yes": "no" );
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
int Abc_CommandUnfold( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nFrames;
    int nConfs;
    int nProps;
    int fStruct;
    int fOldAlgo;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarUnfold( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames   =      1;
    nConfs    =   1000;
    nProps    =   1000;
    fStruct   =      0;
    fOldAlgo  =      0;
    fVerbose  =      0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPsavh" ) ) != EOF )
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
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProps < 0 )
                goto usage;
            break;
        case 's':
            fStruct ^= 1;
            break;
        case 'a':
            fOldAlgo ^= 1;
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
    if ( Abc_NtkIsComb(pNtk) && Abc_NtkPoNum(pNtk) > 1 )
    {
        Abc_Print( -1, "Combinational miter has more than one PO.\n" );
        return 0;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        extern Gia_Man_t * Gia_ManDupWithConstr( Gia_Man_t * p );
        Gia_Man_t * pNew;
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 0 );
        Gia_Man_t * pGia = Gia_ManFromAigSimple( pAig );
        Aig_ManStop( pAig );
        pNew = Gia_ManDupWithConstr( pGia );
        Gia_ManStop( pGia );
        if ( pNew == NULL )
        {
            Abc_Print( -1, "Cannot extract constrains from the miter.\n" );
            return 0;
        }
        pAig = Gia_ManToAigSimple( pNew );
        Gia_ManStop( pNew );
        pNtkRes = Abc_NtkFromAigPhase( pAig );
        Aig_ManStop( pAig );
        ABC_FREE( pNtkRes->pName );
        pNtkRes->pName = Extra_UtilStrsav( pNtk->pName );
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Constraints are already extracted.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) > 1 && !fStruct )
    {
        Abc_Print( -1, "Functional constraint extraction works for single-output miters (use \"orpos\").\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarUnfold( pNtk, nFrames, nConfs, nProps, fStruct, fOldAlgo, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( 1,"Transformation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: unfold [-FCP num] [-savh]\n" );
    Abc_Print( -2, "\t         unfold hidden constraints as separate outputs\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes to consider [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts in SAT solving [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-P num : the max number of constraint propagations [default = %d]\n", nProps );
    Abc_Print( -2, "\t-s     : toggle detecting structural constraints [default = %s]\n", fStruct? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle fast implication detection [default = %s]\n", !fOldAlgo? "yes": "no" );
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
int Abc_CommandFold( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fCompl;
    int fVerbose;
    int fSeqCleanup;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarFold( Abc_Ntk_t * pNtk, int fCompl, int fVerbose, int fSeqCleanup );
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fCompl    =   0;
    fVerbose  =   0;
    fSeqCleanup = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cvsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fCompl ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSeqCleanup ^= 1;
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
    if ( Abc_NtkConstrNum(pNtk) == 0 )
    {
        Abc_Print( 0, "The network has no constraints.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) == Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( 0, "The network has no primary outputs (only constraints).\n" );
        return 0;
    }
    if ( Abc_NtkIsComb(pNtk) )
        Abc_Print( 0, "The network is combinational.\n" );
    // modify the current network
    pNtkRes = Abc_NtkDarFold( pNtk, fCompl, fVerbose, fSeqCleanup );
    if ( pNtkRes == NULL )
    {
        Abc_Print( 1,"Transformation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: fold [-cvh]\n" );
    Abc_Print( -2, "\t         folds constraints represented as separate outputs\n" );
    Abc_Print( -2, "\t         (constraints fail when any of them becomes 1 in any timeframe)\n" );
    Abc_Print( -2, "\t-c     : toggle complementing constraints while folding [default = %s]\n", fCompl? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle performing sequential cleanup [default = %s]\n", fSeqCleanup? "yes": "no" );
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
int Abc_CommandReconcile( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Cex_t * Llb4_Nonlin4NormalizeCex( Aig_Man_t * pAigOrg, Aig_Man_t * pAigRpm, Abc_Cex_t * pCexRpm );
    Abc_Cex_t * pCex;
    Abc_Ntk_t * pNtk1 = NULL, * pNtk2 = NULL;
    Aig_Man_t * pAig1 = NULL, * pAig2 = NULL;
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

    if ( argc != globalUtilOptind + 2 && argc != globalUtilOptind )
    {
        Abc_Print( 1,"Does not seen to have two files names as arguments.\n" );
        return 1;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1,"There is no current counter-example.\n" );
        return 1;
    }

    if ( argc == globalUtilOptind + 2 )
    {
        // derive networks
        pNtk1 = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1, 0 );
        if ( pNtk1 == NULL )
            return 1;
        pNtk2 = Io_Read( argv[globalUtilOptind+1], Io_ReadFileType(argv[globalUtilOptind+1]), 1, 0 );
        if ( pNtk2 == NULL )
        {
            Abc_NtkDelete( pNtk1 );
            return 1;
        }
        // create counter-examples
        pAig1 = Abc_NtkToDar( pNtk1, 0, 0 );
        pAig2 = Abc_NtkToDar( pNtk2, 0, 0 );
    }
    else if ( argc == globalUtilOptind )
    {
        if ( pAbc->pNtkCur == NULL )
        {
            Abc_Print( 1, "There is no AIG in the main-space.\n");
            return 0;
        }
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( 1, "There is no AIG in the &-space.\n");
            return 0;
        }
        // create counter-examples
        pAig1 = Abc_NtkToDar( pAbc->pNtkCur, 0, 0 );
        pAig2 = Gia_ManToAigSimple( pAbc->pGia );
    }
    else assert( 0 );
    pCex = Llb4_Nonlin4NormalizeCex( pAig1, pAig2, pAbc->pCex );
    Aig_ManStop( pAig1 );
    Aig_ManStop( pAig2 );
    if ( pNtk2 )  Abc_NtkDelete( pNtk2 );
    if ( pCex == NULL )
    {
        Abc_Print( 1,"Counter-example computation has failed.\n" );
        if ( pNtk1 )  Abc_NtkDelete( pNtk1 );
        return 1;
    }

    // replace the current network
    if ( pNtk1 )
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtk1 );
    // update the counter-example
    pAbc->nFrames = pCex->iFrame;
    Abc_FrameReplaceCex( pAbc, &pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: reconcile [-h] <fileOrigin> <fileReparam>\n" );
    Abc_Print( -2, "\t        reconciles current CEX with <fileOrigin>\n" );
    Abc_Print( -2, "\t        More specifically:\n" );
    Abc_Print( -2, "\t        (i) assumes that <fileReparam> is an AIG derived by input\n" );
    Abc_Print( -2, "\t        reparametrization of <fileOrigin> without seq synthesis;\n" );
    Abc_Print( -2, "\t        (ii) assumes that current CEX is valid for <fileReparam>;\n" );
    Abc_Print( -2, "\t        (iii) derives new CEX for <fileOrigin> and sets this CEX\n" );
    Abc_Print( -2, "\t        and <fileOrigin> to be current CEX and current network\n" );
    Abc_Print( -2, "\t<fileOrigin>   : file name with the original AIG\n");
    Abc_Print( -2, "\t<fileReparam>  : file name with the reparametrized AIG\n");
    Abc_Print( -2, "\t        (if both file names are not given on the command line,\n");
    Abc_Print( -2, "\t        original/reparam AIG has to be in the main-space/&-space)\n");
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
int Abc_CommandDualRail( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Abc_NtkFindDcLatches( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pNtk, * pNtkNew = NULL;
    Aig_Man_t * pAig, * pAigNew;
    Vec_Int_t * vDcFlops = NULL;
    int c;
    int nDualPis   = 0;
    int fDualFfs   = 0;
    int fDualDcFfs = 0;
    int fMiterFfs  = 0;
    int fComplPo   = 0;
    int fCheckZero = 0;
    int fCheckOne  = 0;
    int fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Itxfczovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nDualPis = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDualPis < 0 )
                goto usage;
            break;
        case 't':
            fDualFfs ^= 1;
            break;
        case 'x':
            fDualDcFfs ^= 1;
            break;
        case 'f':
            fMiterFfs ^= 1;
            break;
        case 'c':
            fComplPo ^= 1;
            break;
        case 'z':
            fCheckZero ^= 1;
            break;
        case 'o':
            fCheckOne ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Main AIG: There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        return 0;
    }

    if ( fDualDcFfs )
        vDcFlops = Abc_NtkFindDcLatches( pNtk );

    // transform
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    pAigNew = Saig_ManDupDual( pAig, vDcFlops, nDualPis, fDualFfs, fMiterFfs, fComplPo, fCheckZero, fCheckOne );
    Aig_ManStop( pAig );
    pNtkNew = Abc_NtkFromAigPhase( pAigNew );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    Aig_ManStop( pAigNew );
    Vec_IntFreeP( &vDcFlops );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: dualrail [-I num] [-txfczovh]\n" );
    Abc_Print( -2, "\t         transforms the current AIG into a dual-rail miter\n" );
    Abc_Print( -2, "\t         expressing the property \"at least one PO has ternary value\"\n" );
    Abc_Print( -2, "\t         (to compute an initialization sequence, use switches \"-tfc\")\n" );
    Abc_Print( -2, "\t-I num : the number of first PIs interpreted as ternary [default = %d]\n", nDualPis );
    Abc_Print( -2, "\t-t     : toggle ternary flop init values for all flops [default = %s]\n", fDualFfs? "yes": "const0 init values" );
    Abc_Print( -2, "\t-x     : toggle ternary flop init values for DC-valued flops [default = %s]\n", fDualDcFfs? "yes": "const0 init values" );
    Abc_Print( -2, "\t-f     : toggle mitering flops instead of POs [default = %s]\n", fMiterFfs? "flops": "POs" );
    Abc_Print( -2, "\t-c     : toggle complementing the miter output [default = %s]\n", fComplPo? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle checking PO==0 instead of PO==X [default = %s]\n", fCheckZero? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle checking PO==1 instead of PO==X [default = %s]\n", fCheckOne? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBlockPo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkNew = NULL;
    Aig_Man_t * pAig;
    int c;
    int nCycles = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nCycles = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCycles < 0 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Main AIG: There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        return 0;
    }
    if ( nCycles == 0 )
    {
        Abc_Print( 1, "The number of time frame is 0. The circuit is left unchanged.\n" );
        return 0;
    }

    // transform
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    Saig_ManBlockPo( pAig, nCycles );
    pNtkNew = Abc_NtkFromAigPhase( pAig );
    Aig_ManStop( pAig );
    // transfer the name
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: blockpo [-F num] [-fvh]\n" );
    Abc_Print( -2, "\t         forces the miter outputs to be \"true\" in the first F frames\n" );
    Abc_Print( -2, "\t-F num : the number of time frames [default = %d]\n", nCycles );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Uif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupUif( Gia_Man_t * p );
    extern Gia_Man_t * Gia_ManDupBlackBox( Gia_Man_t * p );
    Gia_Man_t * pNew = NULL, * pTemp = NULL;
    int c, fBlackBox = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBlackBox ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Uif(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->vBarBufs == NULL || Vec_IntSize(pAbc->pGia->vBarBufs) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Uif(): Hierarchy is not defined.\n" );
        return 1;
    }
    pNew = Gia_ManDupUif( pAbc->pGia );
    if ( fBlackBox )
    {
        pNew = Gia_ManDupBlackBox( pTemp = pNew );
        Gia_ManStop( pTemp );
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;

usage:
    Abc_Print( -2, "usage: &uif [-bvh]\n" );
    Abc_Print( -2, "\t         eagerly adds UIF constraints when hierarchy is present\n" );
    Abc_Print( -2, "\t-b     : toggle blackboxing while adding constraints [default = %s]\n", fBlackBox? "yes": "no" );
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
int Abc_CommandAbc9GenQbf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_GenQbfMiter( Gia_Man_t * pGia, int nFrames, int nLutNum, int nLutSize, char * pStr, int fUseOut, int fVerbose );
    int nFrames   =    1;
    int nLutNum   =    1;
    int nLutSize  =    6;
    char * pStr   = NULL;
    int fUseOut   =    0;
    int fVerbose  =    0;
    int c;
    Gia_Man_t * pTemp;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FKNSovh" ) ) != EOF )
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutNum < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a string.\n" );
                goto usage;
            }
            pStr = Abc_UtilStrsav(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pStr == NULL )
                goto usage;
            break;
        case 'o':
            fUseOut ^= 1;
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
        Abc_Print( -1, "There is no current GIA.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Works only for sequential networks.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) < nLutSize * nLutNum )
    {
        Abc_Print( -1, "The number of flops (%d) is less than required (%d).\n", Gia_ManRegNum(pAbc->pGia), nLutSize * nLutNum );
        return 1;
    }
    if ( nFrames != 1 || nLutNum != 1 )
    {
        Abc_Print( -1, "Currently this commands works for one frame and one LUT.\n" );
        return 1;
    }
    pTemp = Gia_GenQbfMiter( pAbc->pGia, nFrames, nLutNum, nLutSize, pStr, fUseOut, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    ABC_FREE( pStr );
    return 0;

usage:
    Abc_Print( -2, "usage: &genqbf [-FKN num] [-ovh]\n" );
    Abc_Print( -2, "\t         generates QBF miter for computing an inductive invariant\n" );
    Abc_Print( -2, "\t-F num : the number of time frames for induction [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-K num : the LUT size [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-N num : the number of LUTs [default = %d]\n", nLutNum );
    Abc_Print( -2, "\t-o     : toggle using the last output [default = %s]\n", fUseOut? "yes": "no" );
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
int Abc_CommandAbc9AbsCreate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    //Gia_Man_t * pTemp = NULL;
    char * pStr, * pFlopNum;
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
        Abc_Print( -1, "Abc_CommandAbc9AbsCreate(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vFlopClasses != NULL )
    {
        Abc_Print( -1, "Abstraction flop map is already defined.\n" );
        return 0;
    }
    pAbc->pGia->vFlopClasses = Vec_IntStart( Gia_ManRegNum(pAbc->pGia) );
    // read the flop list
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Flop list should be specified on the command line.\n" );
        return 0;
    }
    pStr = argv[globalUtilOptind];
    // parse flop list
    pFlopNum = strtok( pStr, " ," );
    while ( pFlopNum )
    {
        int iFlop = atoi(pFlopNum);
        assert( iFlop >= 0 && iFlop < Gia_ManRegNum(pAbc->pGia) );
        Vec_IntWriteEntry( pAbc->pGia->vFlopClasses, iFlop, 1 );
        pFlopNum = strtok( NULL, " ," );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_create [-vh] <comma-separated_list_of_zero-based_flop_ids>\n" );
    Abc_Print( -2, "\t        creates new flop map by reading user's input\n" );
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
int Abc_CommandAbc9AbsDerive( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
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
        Abc_Print( -1, "Abc_CommandAbc9AbsDerive(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vFlopClasses == NULL )
    {
        Abc_Print( -1, "Abstraction flop map is missing.\n" );
        return 0;
    }
    pTemp = Gia_ManDupAbsFlops( pAbc->pGia, pAbc->pGia->vFlopClasses );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_derive [-vh]\n" );
    Abc_Print( -2, "\t        derives abstracted model using the pre-computed flop map\n" );
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
int Abc_CommandAbc9AbsRefine( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    Gia_Man_t * pTemp = NULL;
    int c;
    int nFfToAddMax = 0;
    int fTryFour    = 1;
    int fSensePath  = 0;
    int fVerbose    = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mtsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nFfToAddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFfToAddMax < 0 )
                goto usage;
            break;
        case 't':
            fTryFour ^= 1;
            break;
        case 's':
            fSensePath ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9AbsRefine(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsRefine(): There is no counter-example.\n" );
        return 1;
    }
    pAbc->Status = Gia_ManCexAbstractionRefine( pAbc->pGia, pAbc->pCex, nFfToAddMax, fTryFour, fSensePath, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_refine [-M <num>] [-tsvh]\n" );
    Abc_Print( -2, "\t         refines the pre-computed flop map using the counter-example\n" );
    Abc_Print( -2, "\t-M num : the max number of flops to add (0 = not used) [default = %d]\n", nFfToAddMax );
    Abc_Print( -2, "\t-t     : toggle trying four abstractions instead of one [default = %s]\n", fTryFour? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using the path sensitization algorithm [default = %s]\n", fSensePath? "yes": "no" );
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
int Abc_CommandAbc9GlaDerive( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
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
        Abc_Print( -1, "Abc_CommandAbc9GlaDerive(): There is no AIG.\n" );
        return 1;
    }
//    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
//    {
//        Abc_Print( -1, "The network is combinational.\n" );
//        return 0;
//    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) ) 
    { 
        Abc_Print( 1, "The miters is already solved; skipping the command.\n" ); 
        return 0;
    }
    if ( pAbc->pGia->vGateClasses == NULL )
    {
        Abc_Print( -1, "Abstraction gate map is missing.\n" );
        return 0;
    }
    pTemp = Gia_ManDupAbsGates( pAbc->pGia, pAbc->pGia->vGateClasses );
    Gia_ManStop( pTemp );
    pTemp = Gia_ManDupAbsGates( pAbc->pGia, pAbc->pGia->vGateClasses );
    Abc_FrameUpdateGia( pAbc, pTemp );
//    Abc_Print( 1,"This command is currently not enabled.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_derive [-vh]\n" );
    Abc_Print( -2, "\t        derives abstracted model using the pre-computed gate map\n" );
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
int Abc_CommandAbc9GlaRefine( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManNewRefine( Gia_Man_t * p, Abc_Cex_t * pCex, int iFrameStart, int iFrameExtra, int fVerbose );
    int iFrameStart = 0;
    int iFrameExtra = 0;
    int fMinCut = 1;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FGmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrameStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrameStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrameExtra = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrameExtra < 0 )
                goto usage;
            break;
        case 'm':
            fMinCut ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9GlaRefine(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GlaRefine(): There is no counter-example.\n" );
        return 1;
    }
    pAbc->Status = Gia_ManNewRefine( pAbc->pGia, pAbc->pCex, iFrameStart, iFrameExtra, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_refine [-FG num] [-vh]\n" );
    Abc_Print( -2, "\t         refines the pre-computed gate map using the counter-example\n" );
    Abc_Print( -2, "\t-F num : starting timeframe for suffix refinement [default = %d]\n", iFrameStart );
    Abc_Print( -2, "\t-G num : the number of additional timeframes to try [default = %d]\n", iFrameExtra );
//    Abc_Print( -2, "\t-m     : toggle using min-cut to derive the refinements [default = %s]\n", fMinCut? "yes": "no" );
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
int Abc_CommandAbc9GlaShrink( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int fUsePdr = 0;
    int fUseSat = 1;
    int fUseBdd = 0;
    int nFrameMax = 0;
    int nTimeOut = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTpsbvh" ) ) != EOF )
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
        case 'p':
            fUsePdr ^= 1;
            break;
        case 's':
            fUseSat ^= 1;
            break;
        case 'b':
            fUseBdd ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9GlaShrink(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->vGateClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GlaShrink(): There is no gate-level abstraction.\n" );
        return 0;
    }
    Gia_ManShrinkGla( pAbc->pGia, nFrameMax, nTimeOut, fUsePdr, fUseSat, fUseBdd, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_shrink [-FT num] [-psbvh]\n" );
    Abc_Print( -2, "\t         shrinks the abstraction by removing redundant objects\n" );
    Abc_Print( -2, "\t-F num : the maximum timeframe to check to [default = %d]\n", nFrameMax );
    Abc_Print( -2, "\t-T num : the timeout per call, in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-p     : toggle using PDR for checking [default = %s]\n", fUsePdr? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using BMC for checking [default = %s]\n", fUseSat? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle using BDDs for checking [default = %s]\n", fUseBdd? "yes": "no" );
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
int Abc_CommandAbc9Gla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abs_Par_t Pars, * pPars = &Pars;
    int c, fNewAlgo = 1;
    char * pLogFileName = NULL;
    Abs_ParSetDefaults( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FSCMDETRQPBALtfardmnscbpquwvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesStart < 0 )
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
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedStart < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedDelta < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedPerce = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedPerce < 0 )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRatioMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRatioMin < 0 )
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRatioMin2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRatioMin2 < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRatioMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRatioMax < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesNoChangeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesNoChangeLim < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pFileVabs = argv[globalUtilOptind];
            globalUtilOptind++;
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
        case 't':
            pPars->fUseTermVars ^= 1;
            break;
        case 'f':
            pPars->fPropFanout ^= 1;
            break;
        case 'a':
            pPars->fAddLayer ^= 1;
            break;
        case 'r':
            pPars->fNewRefine ^= 1;
            break;
        case 'd':
            pPars->fDumpVabs ^= 1;
            break;
        case 'm':
            pPars->fDumpMabs ^= 1;
            break;
        case 'n':
            fNewAlgo ^= 1;
            break;
        case 's':
            pPars->fUseSkip ^= 1;
            break;
        case 'c':
            pPars->fUseSimple ^= 1;
            break;
        case 'b':
            pPars->fSkipHash ^= 1;
            break;
        case 'p':
            pPars->fUseFullProof ^= 1;
            break;
        case 'q':
            pPars->fCallProver ^= 1;
            break;
        case 'u':
            pPars->fSimpProver ^= 1;
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
        Abc_Print( -1, "There is no AIG.\n" );
        return 0;
    }
//    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
//    {
//        Abc_Print( -1, "The network is combinational.\n" );
//        return 0;
//    }
    if ( pPars->nFramesMax < 0 )
    {
        Abc_Print( 1, "The number of starting frames should be a positive integer.\n" );
        return 0;
    }
    if ( pPars->nFramesMax && pPars->nFramesStart > pPars->nFramesMax )
    {
        Abc_Print( 1, "The starting frame is larger than the max number of frames.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) == 1 )
    {
        if ( fNewAlgo )
            pAbc->Status = Gia_ManPerformGla( pAbc->pGia, pPars );
        else
            pAbc->Status  = Gia_ManPerformGlaOld( pAbc->pGia, pPars, 0 );
        pAbc->nFrames = pPars->iFrame;
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
        if ( pLogFileName )
            Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&gla" );
    }
    else // iterate over outputs
    {
        Gia_Obj_t * pObj; int o, Status;
        Vec_Ptr_t * vSeqModelVec = Vec_PtrStart( Gia_ManPoNum(pAbc->pGia) );
        Vec_Int_t * vStatuses = Vec_IntAlloc( Gia_ManPoNum(pAbc->pGia) );
        Gia_ManForEachPo( pAbc->pGia, pObj, o )
        {
            Gia_Man_t * pOne = Gia_ManDupDfsOnePo( pAbc->pGia, o );
            if ( fNewAlgo )
                Status = Gia_ManPerformGla( pOne, pPars );
            else
                Status = Gia_ManPerformGlaOld( pOne, pPars, 0 );
            Vec_IntPush( vStatuses, Status );
            if ( pLogFileName )
                Abc_NtkWriteLogFile( pLogFileName, pOne->pCexSeq, Status, pPars->iFrame, "&gla" );
            if ( pOne->pCexSeq )
                Vec_PtrWriteEntry( vSeqModelVec, o, pOne->pCexSeq );
            pOne->pCexSeq = NULL;
            Gia_ManStop( pOne );
        }
        assert( Vec_IntSize(vStatuses) == Gia_ManPoNum(pAbc->pGia) );
        Abc_FrameReplaceCexVec( pAbc, &vSeqModelVec );
        Abc_FrameReplacePoStatuses( pAbc, &vStatuses );
        pAbc->nFrames = -1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &gla [-FSCMDETRQPB num] [-AL file] [-fardmnscbpquwvh]\n" );
    Abc_Print( -2, "\t          fixed-time-frame gate-level proof- and cex-based abstraction\n" );
    Abc_Print( -2, "\t-F num  : the max number of timeframes to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-S num  : the starting time frame (0=unused) [default = %d]\n", pPars->nFramesStart );
    Abc_Print( -2, "\t-C num  : the max number of SAT solver conflicts (0=unused) [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-M num  : the max number of learned clauses to keep (0=unused) [default = %d]\n", pPars->nLearnedStart );
    Abc_Print( -2, "\t-D num  : delta value for learned clause removal [default = %d]\n", pPars->nLearnedDelta );
    Abc_Print( -2, "\t-E num  : ratio percentage for learned clause removal [default = %d]\n", pPars->nLearnedPerce );
    Abc_Print( -2, "\t-T num  : an approximate timeout, in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-R num  : stop when abstraction size exceeds num %% (0<=num<=100) [default = %d]\n", pPars->nRatioMin );
    Abc_Print( -2, "\t-Q num  : stop when abstraction size exceeds num %% during refinement (0<=num<=100) [default = %d]\n", pPars->nRatioMin2 );
    Abc_Print( -2, "\t-P num  : maximum percentage of added objects before a restart (0<=num<=100) [default = %d]\n", pPars->nRatioMax );
    Abc_Print( -2, "\t-B num  : the number of stable frames to call prover or dump abstraction [default = %d]\n", pPars->nFramesNoChangeLim );
    Abc_Print( -2, "\t-A file : file name for dumping abstrated model (&gla -d) or abstraction map (&gla -m)\n" );
    Abc_Print( -2, "\t-L file : the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-f      : toggle propagating fanout implications [default = %s]\n", pPars->fPropFanout? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggle refinement by adding one layers of gates [default = %s]\n", pPars->fAddLayer? "yes": "no" );
    Abc_Print( -2, "\t-r      : toggle using improved refinement heuristics [default = %s]\n", pPars->fNewRefine? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggle dumping abstracted model into a file [default = %s]\n", pPars->fDumpVabs? "yes": "no" );
    Abc_Print( -2, "\t-m      : toggle dumping abstraction map into a file [default = %s]\n", pPars->fDumpMabs? "yes": "no" );
    Abc_Print( -2, "\t-n      : toggle using new algorithms [default = %s]\n", fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-s      : toggle skipping previously proved timeframes [default = %s]\n", pPars->fUseSkip? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggle using naive (2-input AND node) CNF encoding [default = %s]\n", pPars->fUseSimple? "yes": "no" );
    Abc_Print( -2, "\t-b      : toggle CNF construction without hashing [default = %s]\n", pPars->fSkipHash? "yes": "no" );
    Abc_Print( -2, "\t-p      : toggle using full-proof for UNSAT cores [default = %s]\n", pPars->fUseFullProof? "yes": "no" );
    Abc_Print( -2, "\t-q      : toggle calling the prover [default = %s]\n", pPars->fCallProver? "yes": "no" );
    Abc_Print( -2, "\t-u      : toggle enabling simplifation before calling the prover [default = %s]\n", pPars->fSimpProver? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w      : toggle printing more verbose information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Vta( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abs_Par_t Pars, * pPars = &Pars;
    int c;
    Abs_ParSetDefaults( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FSPCLDETRAtradvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesStart < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesPast = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesPast < 0 )
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedStart < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedDelta < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLearnedPerce = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLearnedPerce < 0 )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRatioMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRatioMin < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pFileVabs = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 't':
            pPars->fUseTermVars ^= 1;
            break;
        case 'r':
            pPars->fUseRollback ^= 1;
            break;
        case 'a':
            pPars->fAddLayer ^= 1;
            break;
        case 'd':
            pPars->fDumpVabs ^= 1;
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
        Abc_Print( -1, "There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) > 1 )
    {
        Abc_Print( 1, "The network is more than one PO (run \"orpos\").\n" );
        return 0;
    }
    if ( pPars->nFramesMax < 0 )
    {
        Abc_Print( 1, "The number of starting frames should be a positive integer.\n" );
        return 0;
    }
    if ( pPars->nFramesMax && pPars->nFramesStart > pPars->nFramesMax )
    {
        Abc_Print( 1, "The starting frame is larger than the max number of frames.\n" );
        return 0;
    }
    pAbc->Status  = Gia_VtaPerform( pAbc->pGia, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &vta [-FSPCLDETR num] [-A file] [-tradvh]\n" );
    Abc_Print( -2, "\t          variable-time-frame gate-level proof- and cex-based abstraction\n" );
    Abc_Print( -2, "\t-F num  : the max number of timeframes to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-S num  : the starting time frame (0=unused) [default = %d]\n", pPars->nFramesStart );
    Abc_Print( -2, "\t-P num  : the number of previous frames for UNSAT core [default = %d]\n", pPars->nFramesPast );
    Abc_Print( -2, "\t-C num  : the max number of SAT solver conflicts (0=unused) [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-L num  : the max number of learned clauses to keep (0=unused) [default = %d]\n", pPars->nLearnedStart );
    Abc_Print( -2, "\t-D num  : delta value for learned clause removal [default = %d]\n", pPars->nLearnedDelta );
    Abc_Print( -2, "\t-E num  : ratio percentage for learned clause removal [default = %d]\n", pPars->nLearnedPerce );
    Abc_Print( -2, "\t-T num  : an approximate timeout, in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-R num  : minimum percentage of abstracted objects (0<=num<=100) [default = %d]\n", pPars->nRatioMin );
    Abc_Print( -2, "\t-A file : file name for dumping abstrated model [default = \"vabs.aig\"]\n" );
    Abc_Print( -2, "\t-t      : toggle using terminal variables [default = %s]\n", pPars->fUseTermVars? "yes": "no" );
    Abc_Print( -2, "\t-r      : toggle using rollback after the starting frames [default = %s]\n", pPars->fUseRollback? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggle refinement by adding one layers of gates [default = %s]\n", pPars->fAddLayer? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggle dumping abstracted model into a file [default = %s]\n", pPars->fDumpVabs? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Vta2Gla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
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
        Abc_Print( -1, "Abc_CommandAbc9Vta2Gla(): There is no AIG.\n" );
        return 0;
    }
    if ( pAbc->pGia->vObjClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Vta2Gla(): There is no variable-time-frame abstraction is defined.\n" );
        return 0;
    }
    Vec_IntFreeP( &pAbc->pGia->vGateClasses );
    pAbc->pGia->vGateClasses = Gia_VtaConvertToGla( pAbc->pGia, pAbc->pGia->vObjClasses );
    Vec_IntFreeP( &pAbc->pGia->vObjClasses );
    return 0;

usage:
    Abc_Print( -2, "usage: &vta_gla [-vh]\n" );
    Abc_Print( -2, "\t        maps variable- into fixed-time-frame gate-level abstraction\n" );
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
int Abc_CommandAbc9Gla2Vta( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    int nFrames = pAbc->nFrames;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Gla2Vta(): There is no AIG.\n" );
        return 0;
    }
    if ( pAbc->pGia->vGateClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Gla2Vta(): There is no gate-level abstraction is defined.\n" );
        return 0;
    }
    if ( pAbc->nFrames < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Gla2Vta(): The number of timeframes (%d) should be a positive integer.\n", nFrames );
        return 0;
    }
    Vec_IntFreeP( &pAbc->pGia->vObjClasses );
    pAbc->pGia->vObjClasses = Gia_VtaConvertFromGla( pAbc->pGia, pAbc->pGia->vGateClasses, nFrames );
    Vec_IntFreeP( &pAbc->pGia->vGateClasses );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_vta [-F num] [-vh]\n" );
    Abc_Print( -2, "\t          maps fixed- into variable-time-frame gate-level abstraction\n" );
    Abc_Print( -2, "\t-F num  : timeframes in the resulting variable-time-frame abstraction [default = %d]\n", nFrames );
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
int Abc_CommandAbc9Fla2Gla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
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
        Abc_Print( -1, "Abc_CommandAbc9Fla2Gla(): There is no AIG.\n" );
        return 0;
    }
    if ( pAbc->pGia->vFlopClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Fla2Gla(): There is no gate-level abstraction is defined.\n" );
        return 0;
    }
    Vec_IntFreeP( &pAbc->pGia->vGateClasses );
    pAbc->pGia->vGateClasses = Gia_FlaConvertToGla( pAbc->pGia, pAbc->pGia->vFlopClasses );
    Vec_IntFreeP( &pAbc->pGia->vFlopClasses );
    return 0;

usage:
    Abc_Print( -2, "usage: &fla_gla [-vh]\n" );
    Abc_Print( -2, "\t          maps flop-level into gate-level abstraction\n" );
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
int Abc_CommandAbc9Gla2Fla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
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
        Abc_Print( -1, "Abc_CommandAbc9Gla2Fla(): There is no AIG.\n" );
        return 0;
    }
    if ( pAbc->pGia->vGateClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Gla2Fla(): There is no gate-level abstraction is defined.\n" );
        return 0;
    }
    Vec_IntFreeP( &pAbc->pGia->vFlopClasses );
    pAbc->pGia->vFlopClasses = Gia_GlaConvertToFla( pAbc->pGia, pAbc->pGia->vGateClasses );
    Vec_IntFreeP( &pAbc->pGia->vGateClasses );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_fla [-vh]\n" );
    Abc_Print( -2, "\t          maps gate-level into flop-level abstraction\n" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

#include "base/abci/abciUnfold2.c"

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
