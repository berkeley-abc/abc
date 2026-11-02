/**CFile****************************************************************

  FileName    [abcCec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Combinational equivalence checking.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "proof/cec/cec.h"
#include "proof/acec/acec.h"
#include "proof/fraig/fraig.h"
#include "bool/kit/kit.h"
#include "aig/saig/saig.h"
#include "base/sn/snRead.h"
#include "base/sn/snGia.h"
#include "proof/dch/dch.h"
#include "bdd/cudd/cudd.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandRunEco                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRunTest                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter2                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDemiter                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMatch                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigDress             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCec                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDCec                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandProve                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIProve                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDebug                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEco                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBm                     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBm2                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSaucy                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIso                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTraceStart             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTraceCheck             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Miter              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Miter2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cec                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ICec               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Verify             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Iso                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9IsoNpn             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9IsoSt              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Store              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Compare            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9RevEng             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SplitProve         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Demiter            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Acec               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BMiter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BRecover           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9StrEco             ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
#ifdef __cplusplus
extern "C"
#endif
int Gia_ManVerifyTruthFile( Gia_Man_t * p, char * pFileName, int fVerbose );
extern Bnd_Man_t * pBnd;

/**Function*************************************************************

  Synopsis    [Registers combinational equivalence checking commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitCec( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "runeco",        Abc_CommandRunEco,           0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "xec",           Abc_CommandRunTest,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "miter",         Abc_CommandMiter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "miter2",        Abc_CommandMiter2,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "demiter",       Abc_CommandDemiter,          1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "dress",         Abc_CommandFraigDress,       1 );
    Cmd_CommandAdd( pAbc, "Verification", "cec",           Abc_CommandCec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "dcec",          Abc_CommandDCec,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "match",         Abc_CommandMatch,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "prove",         Abc_CommandProve,            1 );
    Cmd_CommandAdd( pAbc, "Verification", "iprove",        Abc_CommandIProve,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "debug",         Abc_CommandDebug,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "eco",           Abc_CommandEco,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "bm",            Abc_CommandBm,               1 );
    Cmd_CommandAdd( pAbc, "Verification", "bm2",           Abc_CommandBm2,              1 );
    Cmd_CommandAdd( pAbc, "Verification", "saucy3",        Abc_CommandSaucy,            1 );
    Cmd_CommandAdd( pAbc, "Verification", "iso",           Abc_CommandIso,              1 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&miter",        Abc_CommandAbc9Miter,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&miter2",       Abc_CommandAbc9Miter2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cec",          Abc_CommandAbc9Cec,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&icec",         Abc_CommandAbc9ICec,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&verify",       Abc_CommandAbc9Verify,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&iso",          Abc_CommandAbc9Iso,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&isonpn",       Abc_CommandAbc9IsoNpn,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&isost",        Abc_CommandAbc9IsoSt,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&store",        Abc_CommandAbc9Store,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&compare",      Abc_CommandAbc9Compare,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reveng",       Abc_CommandAbc9RevEng,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&splitprove",   Abc_CommandAbc9SplitProve,   0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&demiter",      Abc_CommandAbc9Demiter,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&acec",         Abc_CommandAbc9Acec,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bmiter",       Abc_CommandAbc9BMiter,                 0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&brecover",     Abc_CommandAbc9BRecover,               0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&str_eco",      Abc_CommandAbc9StrEco,                 0 );
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
int Abc_CommandRunEco( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Acb_NtkRunEco( char * pFileNames[4], int nTimeout, int fCheck, int fRandom, int fInputs, int fUnitW, int fVerbose, int fVeryVerbose );
    char * pFileNames[4] = {NULL};
    int c, nTimeout = 0, fCheck = 0, fRandom = 0, fInputs = 0, fUnitW = 0, fVerbose = 0, fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Tcriuvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeout < 0 )
                goto usage;
            break;
        case 'c':
            fCheck ^= 1;
            break;
        case 'r':
            fRandom ^= 1;
            break;
        case 'i':
            fInputs ^= 1;
            break;
        case 'u':
            fUnitW ^= 1;
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
//    pArgvNew = argv + globalUtilOptind;
//    nArgcNew = argc - globalUtilOptind;
    if ( argc - globalUtilOptind < 2 || argc - globalUtilOptind > 3 )
    {
        Abc_Print( 1, "Expecting three file names on the command line.\n" );
        goto usage;
    }
    for ( c = 0; c < argc - globalUtilOptind; c++ )
    {
        FILE * pFile = fopen( argv[globalUtilOptind+c], "rb" );
        if ( pFile == NULL )
        {
            printf( "Cannot open input file \"%s\".\n", argv[globalUtilOptind+c] );
            return 0;
        }
        else
            fclose( pFile );
        pFileNames[c] = argv[globalUtilOptind+c];
    }
    Acb_NtkRunEco( pFileNames, nTimeout, fCheck, fRandom, fInputs, fUnitW, fVerbose, fVeryVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: runeco [-T num] [-criuvwh] <implementation> <specification> <weights>\n" );
    Abc_Print( -2, "\t         performs computation of patch functions during ECO,\n" );
    Abc_Print( -2, "\t         as described in the following paper: A. Q. Dao et al\n" );
    Abc_Print( -2, "\t         \"Efficient computation of ECO patch functions\", Proc. DAC\'18\n" );
    Abc_Print( -2, "\t         https://people.eecs.berkeley.edu/~alanmi/publications/2018/dac18_eco.pdf\n" );
    Abc_Print( -2, "\t         (currently only applicable to benchmarks from 2017 ICCAD CAD competition\n" );
    Abc_Print( -2, "\t         http://cad-contest-2017.el.cycu.edu.tw/Problem_A/default.html as follows:\n" );
    Abc_Print( -2, "\t         \"runeco unit1/F.v unit1/G.v unit1/weight.txt; cec -n out.v unit1/G.v\")\n" );
    Abc_Print( -2, "\t-T num : the timeout in seconds [default = %d]\n", nTimeout );
    Abc_Print( -2, "\t-c     : toggle checking that the problem has a solution [default = %s]\n", fCheck? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using random permutation of support variables [default = %s]\n", fRandom? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle using primary inputs as support variables [default = %s]\n", fInputs? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggle using unit weights [default = %s]\n", fUnitW? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing more verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRunTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Acb_NtkRunTest( char * pFileNames[4], int fFancy, int fVerbose, int fUseCadical );
    char * pFileNames[4] = {NULL};
    int c, fFancy = 0, fVerbose = 0, fUseCadical = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cfvh" ) ) != EOF )
    {
        switch ( c )
        {
	case 'c':
	    fUseCadical ^= 1;
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
    if ( argc - globalUtilOptind < 2 || argc - globalUtilOptind > 5 )
    {
        Abc_Print( 1, "Expecting two or three file names on the command line.\n" );
        goto usage;
    }
    for ( c = 0; c < argc - globalUtilOptind; c++ )
        pFileNames[c] = argv[globalUtilOptind+c];
    Acb_NtkRunTest( pFileNames, fFancy, fVerbose, fUseCadical );
    return 0;

usage:
    Abc_Print( -2, "usage: xec [-cfvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t           combinational equivalence checking with x-values\n" );
    Abc_Print( -2, "\t-c       : toggle using CaDiCaL SAT-only solving [default = %s]\n", fUseCadical? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggle using experimental feature [default = %s]\n",      fFancy? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
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
    char Buffer[32];
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fCheck;
    int fComb;
    int fImplic;
    int fMulti;
    int nPartSize;
    int fTrans;
    int fIgnoreNames;

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fComb  = 0;
    fCheck = 1;
    fImplic = 0;
    fMulti = 0;
    nPartSize = 0;
    fTrans = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Pcmitnh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 )
                goto usage;
            break;
        case 'c':
            fComb ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 'i':
            fImplic ^= 1;
            break;
        case 't':
            fTrans ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fTrans )
    {
        if ( (Abc_NtkPoNum(pNtk) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandMiter(): The number of outputs should be even.\n" );
            return 0;
        }
        // replace the current network
        pNtkRes = Abc_NtkDupTransformMiter( pNtk );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        Abc_Print( 1, "The miter (current network) is transformed by XORing POs pair-wise.\n" );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 1;

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
    // compute the miter
    pNtkRes = Abc_NtkMiter( pNtk1, pNtk2, fComb, nPartSize, fImplic, fMulti );
    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );

    // get the new network
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Miter computation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( nPartSize == 0 )
        strcpy( Buffer, "unused" );
    else
        sprintf(Buffer, "%d", nPartSize );
    Abc_Print( -2, "usage: miter [-P <num>] [-cimtnh] <file1> <file2>\n" );
    Abc_Print( -2, "\t           computes the miter of the two circuits\n" );
    Abc_Print( -2, "\t-P <num> : output partition size [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-c       : toggles deriving combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles deriving implication miter (file1 => file2) [default = %s]\n", fImplic? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles creating multi-output miter [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggle XORing pair-wise POs of the miter [default = %s]\n", fTrans? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggle ignoring names when matching CIs/COs [default = %s]\n", fIgnoreNames? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\tfile1    : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2    : (optional) the file with the second network\n");
    Abc_Print( -2, "\t           if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t           if one file is given, uses the current network and the file\n\n");
    Abc_Print( -2, "\t           Please note that, when used without \"-n\", this command tries to match\n" );
    Abc_Print( -2, "\t           primary inputs by name and, to achieve this, it will order them alphabetically,\n" );
    Abc_Print( -2, "\t           which results in incorrect QBF miters and confusing counter-examples.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMiter2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Ptr_t * Abc_NtkReadNodeNames( Abc_Ntk_t * pNtk, char * pFileName );
    extern Abc_Ntk_t * Abc_NtkSpecialMiter( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes );

    Abc_Ntk_t * pNtk, * pNtkRes;
    Vec_Ptr_t * vNodes;
    char * pFileName;
    int c, fVerbose = 0;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
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

    // get the second network
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "The file with node names is not given.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "The base network should be logic network from BLIF file.\n" );
        return 1;
    }
    // read the second network
    pFileName = argv[globalUtilOptind];
    if ( (vNodes = Abc_NtkReadNodeNames(pNtk, pFileName)) == NULL )
    {
        Abc_Print( -1, "Cannot read node names from file \"%s\".\n", pFileName );
        return 1;
    }
    pNtkRes = Abc_NtkSpecialMiter( pNtk, vNodes );
    Vec_PtrFree( vNodes );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: miter2 [-h] <file>\n" );
    Abc_Print( -2, "\t         derives specialized miter\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name with node names\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fDual, fVerbose;
    extern int Abc_NtkDarDemiter( Abc_Ntk_t * pNtk );
    extern int Abc_NtkDarDemiterDual( Abc_Ntk_t * pNtk, int fVerbose );
    // set defaults
    fDual = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDual ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
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

    if ( fDual )
    {
        if ( (Abc_NtkPoNum(pNtk) & 1) )
        {
            Abc_Print( -1, "The number of POs should be even.\n" );
            return 0;
        }
        if ( !Abc_NtkDarDemiterDual( pNtk, fVerbose ) )
        {
            Abc_Print( -1, "Demitering has failed.\n" );
            return 1;
        }
        return 0;
    }
//    if ( Abc_NtkPoNum(pNtk) != 1 )
//    {
//        Abc_Print( -1, "The network is not a single-output miter.\n" );
//        return 1;
//    }
//    if ( !Abc_NodeIsExorType(Abc_ObjFanin0(Abc_NtkPo(pNtk,0))) )
//    {
//        Abc_Print( -1, "The miter's PO is not an EXOR.\n" );
//        return 1;
//    }
//    if ( !Abc_NtkDemiter( pNtk ) )
//    {
//        Abc_Print( -1, "Demitering has failed.\n" );
//        return 1;
//    }
    // get the new network
    if ( !Abc_NtkDarDemiter( pNtk ) )
    {
        Abc_Print( -1, "Demitering has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: demiter [-dvh]\n" );
    Abc_Print( -2, "\t        splits sequential miter into two circuits\n" );
    Abc_Print( -2, "\t-d    : expects a dual-output miter (without XORs) [default = %s]\n", fDual? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    Abc_Ntk_t * pNtk, * pNtkTemp;
    int c, RetValue, iOut = -1;
    char * pLogFileName = NULL;
    abctime clk;

    extern int Abc_NtkIvyProve( Abc_Ntk_t ** ppNtk, void * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Prove_ParamsSetDefault( pParams );
    pParams->fUseRewriting = 1;
    pParams->fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCFGMILrfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitMulti = (float)atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitMulti < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nTotalInspectLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nTotalInspectLimit < 0 )
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "The network has registers. Use \"dprove\".\n" );
        return 1;
    }

    clk = Abc_Clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );

    RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        Abc_Obj_t * pObj;
        int i;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( pSimInfo[i] == 1 )
            {
                iOut = i;
                break;
            }
        if ( i == Abc_NtkCoNum(pNtk) )
            Abc_Print( 1, "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        ABC_FREE( pSimInfo );
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE (output = %d) ", iOut );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );

    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    // update counter example
    if ( RetValue == 0 && Abc_NtkLatchNum(pNtkTemp) == 0 )
    {
        Abc_Cex_t * pCex = Abc_CexDeriveFromCombModel( pNtkTemp->pModel, Abc_NtkPiNum(pNtkTemp), 0, iOut );
        Abc_FrameReplaceCex( pAbc, &pCex );
    }
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "iprove" );
    return 0;

usage:
    Abc_Print( -2, "usage: iprove [-NCFGMI num] [-L file] [-rfbvh]\n" );
    Abc_Print( -2, "\t         performs CEC using a new method\n" );
    Abc_Print( -2, "\t-N num : max number of iterations [default = %d]\n", pParams->nItersMax );
    Abc_Print( -2, "\t-C num : max starting number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitStart );
    Abc_Print( -2, "\t-F num : max starting number of conflicts in fraiging [default = %d]\n", pParams->nFraigingLimitStart );
    Abc_Print( -2, "\t-G num : multiplicative coefficient for fraiging [default = %d]\n", (int)pParams->nFraigingLimitMulti );
    Abc_Print( -2, "\t-M num : max last-gasp number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitLast );
    Abc_Print( -2, "\t-I num : max number of clause inspections in all SAT calls [default = %d]\n", (int)pParams->nTotalInspectLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n",                            pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle the use of FRAIGing [default = %s]\n", pParams->fUseFraiging? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle the use of BDDs [default = %s]\n", pParams->fUseBdds? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    extern void Abc_NtkDress( Abc_Ntk_t * pNtk, char * pFileName, int fVerbose );
    extern void Abc_NtkDress2( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConflictLimit, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtk2;
    char * pFileName;
    int c;
    int nConfs;
    int fVerbose;
    // set defaults
    nConfs   = 1000;
    fVerbose =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind && argc != globalUtilOptind + 1 )
        goto usage;
    if ( argc == globalUtilOptind && Abc_NtkSpec(pNtk) == NULL )
    {
        Abc_Print( -1, "The current network has no spec.\n" );
        return 1;
    }
    // get the input file name
    pFileName = (argc == globalUtilOptind + 1) ? argv[globalUtilOptind] : Abc_NtkSpec(pNtk);
    // modify the current network
//    Abc_NtkDress( pNtk, pFileName, fVerbose );
    pNtk2 = Io_Read( pFileName, Io_ReadFileType(pFileName), 1, 0 );
    if ( pNtk2 == NULL )
        return 1;
    Abc_NtkDress2( pNtk, pNtk2, nConfs, fVerbose );
    Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dress [-C num] [-vh] <file>\n" );
    Abc_Print( -2, "\t         transfers internal node names from file to the current network\n" );
    Abc_Print( -2, "\t<file> : network with names (if not given, the current network spec is used)\n" );
    Abc_Print( -2, "\t-C num : the maximum number of conflicts at each node [default = %d]\n", nConfs );
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
int Abc_CommandCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[16];
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;
    int nSeconds;
    int nPartSize;
    int nConfLimit;
    int nInsLimit;
    int fPartition;
    int fIgnoreNames;

    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );
    extern void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );
    extern void Abc_NtkCecFraigPart( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nPartSize, int fVerbose );
    extern void Abc_NtkCecFraigPartAuto( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nPartSize  = 0;
    nConfLimit = 10000;
    nInsLimit  = 0;
    fPartition = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIPpsnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 )
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk && pNtk->vPhases != NULL )
    {
        Abc_Print( -1, "Cannot compare networks with phases defined.\n" );
        return 1;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 1;

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

    // perform equivalence checking
    if ( fPartition )
        Abc_NtkCecFraigPartAuto( pNtk1, pNtk2, nSeconds, fVerbose );
    else if ( nPartSize )
        Abc_NtkCecFraigPart( pNtk1, pNtk2, nSeconds, nPartSize, fVerbose );
    else if ( fSat )
        Abc_NtkCecSat( pNtk1, pNtk2, nConfLimit, nInsLimit );
    else
        Abc_NtkCecFraig( pNtk1, pNtk2, nSeconds, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    if ( nPartSize == 0 )
        strcpy( Buffer, "unused" );
    else
        sprintf(Buffer, "%d", nPartSize );
    Abc_Print( -2, "usage: cec [-T num] [-C num] [-I num] [-P num] [-psnvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs combinational equivalence checking\n" );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-P num : partition size for multi-output networks [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-p     : toggle automatic partitioning [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    Abc_Print( -2, "\t-n     : toggle how CIs/COs are matched (by name or by order) [default = %s]\n", fIgnoreNames? "by order": "by name" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
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
int Abc_CommandDCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
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
    int fPartition;
    int fMiter;

    extern int Abc_NtkDSat( Abc_Ntk_t * pNtk, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int nLearnedStart, int nLearnedDelta, int nLearnedPerce, int fAlignPol, int fAndOuts, int fNewSolver, int fVerbose );
    extern int Abc_NtkDarCec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int fPartition, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nConfLimit = 10000;
    nInsLimit  = 0;
    fPartition = 0;
    fMiter     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIpmsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 )
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 'm':
            fMiter ^= 1;
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
    if ( fMiter )
    {
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Empty network.\n" );
            return 1;
        }
        if ( Abc_NtkIsStrash(pNtk) )
        {
            pNtk1 = pNtk;
            fDelete1 = 0;
        }
        else
        {
            pNtk1 = Abc_NtkStrash( pNtk, 0, 1, 0 );
            fDelete1 = 1;
        }
        pNtk2 = NULL;
        fDelete2 = 0;
    }
    else
    {
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
            return 1;
    }

    if ( (pNtk1 && Abc_NtkLatchNum(pNtk1)) || (pNtk2 && Abc_NtkLatchNum(pNtk2)) )
    {
        if ( pNtk1 && fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( pNtk2 && fDelete2 ) Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "Currently this command only works for networks without latches. Run \"comb\".\n" );
        return 1;
    }

    // perform equivalence checking
    if ( fSat && fMiter )
        Abc_NtkDSat( pNtk1, nConfLimit, nInsLimit, 0, 0, 0, 0, 0, 0, fVerbose );
    else
        Abc_NtkDarCec( pNtk1, pNtk2, nConfLimit, fPartition, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dcec [-T num] [-C num] [-I num] [-mpsvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs combinational equivalence checking\n" );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-m     : toggle working on two networks or a miter [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-p     : toggle automatic partitioning [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle \"SAT only\" (miter) or \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
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
int Abc_CommandMatch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew, c;
    int fMiter;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarMatch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter = 0;
    nDist = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist < 0 )
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
//        Abc_Ntk_t * pNtkA, * pNtkB;
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
            return 0;
        }
        pNtkRes = Abc_NtkDarMatch( pNtk, NULL, nDist, fVerbose );
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
        pNtkRes = Abc_NtkDarMatch( pNtk1, pNtk2, nDist, fVerbose );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Matching has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: match [-D num] [-mv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         detects structural similarity using simulation\n" );
    Abc_Print( -2, "\t         replaces the current network by the miter of differences\n" );
    Abc_Print( -2, "\t-D num : the distance for extending differences [default = %d]\n", nDist );
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
int Abc_CommandProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    Prove_Params_t Params, * pParams = &Params;
    int c, RetValue;
    abctime clk;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Prove_ParamsSetDefault( pParams );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCFGLIrfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitMulti = (float)atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitMulti < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    }
    if ( Abc_NtkCoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently can only solve the miter with one output.\n" );
        return 0;
    }
    clk = Abc_Clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );

    RetValue = Abc_NtkMiterProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        ABC_FREE( pSimInfo );
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );

    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: prove [-NCFGLI num] [-rfbvh]\n" );
    Abc_Print( -2, "\t         solves combinational miter by rewriting, FRAIGing, and SAT\n" );
    Abc_Print( -2, "\t         replaces the current network by the cone modified by rewriting\n" );
    Abc_Print( -2, "\t         (there is also newer CEC command \"iprove\")\n" );
    Abc_Print( -2, "\t-N num : max number of iterations [default = %d]\n", pParams->nItersMax );
    Abc_Print( -2, "\t-C num : max starting number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitStart );
    Abc_Print( -2, "\t-F num : max starting number of conflicts in fraiging [default = %d]\n", pParams->nFraigingLimitStart );
    Abc_Print( -2, "\t-G num : multiplicative coefficient for fraiging [default = %d]\n", (int)pParams->nFraigingLimitMulti );
    Abc_Print( -2, "\t-L num : max last-gasp number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitLast );
    Abc_Print( -2, "\t-I num : max number of clause inspections in all SAT calls [default = %d]\n", (int)pParams->nTotalInspectLimit );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle the use of FRAIGing [default = %s]\n", pParams->fUseFraiging? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle the use of BDDs [default = %s]\n", pParams->fUseBdds? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern void Abc_NtkAutoDebug( Abc_Ntk_t * pNtk, int (*pFuncError) (Abc_Ntk_t *) );
    extern int Abc_NtkRetimeDebug( Abc_Ntk_t * pNtk );
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
        Abc_Print( -1, "This command is applicable to logic networks.\n" );
        return 1;
    }

    Abc_NtkAutoDebug( pNtk, Abc_NtkRetimeDebug );
    return 0;

usage:
    Abc_Print( -2, "usage: debug [-h]\n" );
    Abc_Print( -2, "\t        performs automated debugging of the given procedure\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEco( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkEco( char * pFileNames[3] );
    char * pFileNames[3] = {NULL};  int c;
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
    if ( globalUtilOptind + 3 != argc )
    {
        Abc_Print( -1, "Expecting three file names on the command line.\n" );
        return 1;
    }
    for ( c = 0; c < 3; c++ )
        pFileNames[c] = argv[globalUtilOptind+c];
    Abc_NtkEco( pFileNames );
    return 0;

usage:
    Abc_Print( -2, "usage: eco [-h]\n" );
    Abc_Print( -2, "\t        performs experimental ECO computation\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t *pNtk, *pNtk1, *pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int c, nArgcNew;
    int p_equivalence = FALSE;
    extern void bmGateWay( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int p_equivalence );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        case 'P':
            p_equivalence = 1;
            break;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew , &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 1;

    if( (unsigned)Abc_NtkPiNum(pNtk1) != (unsigned)Abc_NtkPiNum(pNtk2) || (unsigned)Abc_NtkPoNum(pNtk1) != (unsigned)Abc_NtkPoNum(pNtk2) )
    {
        Abc_Print( -2, "Mismatch in the number of inputs or outputs\n");
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        return 1;
    }

    bmGateWay( pNtk1, pNtk2, p_equivalence );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: bm [-P] <file1> <file2>\n" );
    Abc_Print( -2, "\t        performs Boolean matching (P-equivalence & PP-equivalence)\n" );
    Abc_Print( -2, "\t        for equivalent circuits, I/O matches are printed in IOmatch.txt\n" );
    Abc_Print( -2, "\t-P    : performs P-equivalnce checking\n");
    Abc_Print( -2, "\t        default is PP-equivalence checking (when -P is not provided)\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tfile1 : the file with the first network\n");
    Abc_Print( -2, "\tfile2 : the file with the second network\n");

    Abc_Print( -2, "\t        \n" );
    Abc_Print( -2, "\t        This command was contributed by Hadi Katebi from U Michigan.\n" );
    Abc_Print( -2, "\t        The paper describing the method: H. Katebi and I. L. Markov.\n" );
    Abc_Print( -2, "\t        \"Large-scale Boolean matching\". Proc. DATE 2010. \n" );
    Abc_Print( -2, "\t        http://www.eecs.umich.edu/~imarkov/pubs/conf/date10-match.pdf\n" );
//    Abc_Print( -2, "\t        \n" );

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBm2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t *pNtk, *pNtk1, *pNtk2;
    int fDelete1, fDelete2;
    Abc_Obj_t * pObj;
    char ** pArgvNew;
    int c, nArgcNew, i;

    extern void saucyGateWay( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodePo, FILE * gFile, int fBooleanMatching,
                              int fLookForSwaps, int fFixOutputs, int fFixInputs, int fQuiet, int fPrintTree);

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

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

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew , &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 1;

    if( (unsigned)Abc_NtkPiNum(pNtk1) != (unsigned)Abc_NtkPiNum(pNtk2) ||
        (unsigned)Abc_NtkPoNum(pNtk1) != (unsigned)Abc_NtkPoNum(pNtk2) )
    {
        Abc_Print( -2, "Mismatch in the number of inputs or outputs\n");
        Abc_Print( -2, "*** Networks are NOT equivalent ***\n");
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        return 1;
    }

    Abc_NtkPermute(pNtk2, 1, 1, 0, NULL, NULL, NULL );
    Abc_NtkShortNames(pNtk2);

    Abc_NtkForEachCi( pNtk1, pObj, i ) {
        char * newName = Abc_ObjNamePrefix( pObj, "N1:" );
        Nm_ManDeleteIdName( pNtk1->pManName, pObj->Id);
        Abc_ObjAssignName( pObj, newName, NULL );
    }
    Abc_NtkForEachCo( pNtk1, pObj, i ) {
        char * newName = Abc_ObjNamePrefix( pObj, "N1:" );
        Nm_ManDeleteIdName( pNtk1->pManName, pObj->Id);
        Abc_ObjAssignName( pObj, newName, NULL );
    }

    Abc_NtkForEachCi( pNtk2, pObj, i ) {
        char * newName = Abc_ObjNamePrefix( pObj, "N2:" );
        Nm_ManDeleteIdName( pNtk2->pManName, pObj->Id);
        Abc_ObjAssignName( pObj, newName, NULL );
    }
    Abc_NtkForEachCo( pNtk2, pObj, i ) {
        char * newName = Abc_ObjNamePrefix( pObj, "N2:" );
        Nm_ManDeleteIdName( pNtk2->pManName, pObj->Id);
        Abc_ObjAssignName( pObj, newName, NULL );
    }

    Abc_NtkAppend( pNtk1, pNtk2, 1 );
    saucyGateWay( pNtk1, NULL, NULL, 1, 0, 0, 0, 0, 0);

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: bm2  <file1> <file2>\n" );
    Abc_Print( -2, "\t        performs Boolean matching (PP-equivalence)\n" );
    Abc_Print( -2, "\t        for equivalent circuits, permutation that maps one circuit\n" );
    Abc_Print( -2, "\t        to another is printed to standard output (PIs and POs of the\n" );
    Abc_Print( -2, "\t        first network have prefix \"N1:\", while PIs and POs of the\n" );
    Abc_Print( -2, "\t        second network have prefix \"N2:\")\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tfile1 : the file with the first network\n");
    Abc_Print( -2, "\tfile2 : the file with the second network\n");

    Abc_Print( -2, "\t        \n" );
    Abc_Print( -2, "\t        This command was contributed by Hadi Katebi from U Michigan.\n" );
    Abc_Print( -2, "\t        The paper describing the method: H. Katebi, K. Sakallah and\n");
    Abc_Print( -2, "\t        I. L. Markov.\n" );
    Abc_Print( -2, "\t        \"Generalized Boolean Symmetries Through Nested Partition\n");
    Abc_Print( -2, "\t        Refinement\". Proc. ICCAD 2013. \n" );
    //Abc_Print( -2, "\t        http://www.eecs.umich.edu/~imarkov/pubs/conf/date10-match.pdf\n" );
//    Abc_Print( -2, "\t        \n" );

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSaucy( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t *pNtk;
    char * outputName = NULL;
    FILE * gFile = NULL;
    int fOutputsOneAtTime = 0;
    int fFixOutputs = 0;
    int fFixInputs = 0;
    int fLookForSwaps = 0;
    int fQuiet = 0;
    int fPrintTree = 0;
    int c;

    extern void saucyGateWay( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodePo, FILE * gFile, int fBooleanMatching,
                              int fLookForSwaps, int fFixOutputs, int fFixInputs, int fQuiet, int fPrintTree);

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "OFiosqvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an output name or the keyword all.\n" );
                goto usage;
            }
            outputName = argv[globalUtilOptind];
            if ( !strcmp(argv[globalUtilOptind], "all") )
                fOutputsOneAtTime ^= 1;
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            if ( (gFile = fopen( argv[globalUtilOptind], "w" )) == NULL )
            {
                Abc_Print( -1, "Cannot create output file \"%s\". ", argv[globalUtilOptind] );
                return 1;
            }
            globalUtilOptind++;
            break;
        case 'i':
            fFixOutputs ^= 1;
            break;
        case 'o':
            fFixInputs ^= 1;
            break;
        case 's':
            fLookForSwaps ^= 1;
            break;
        case 'q':
            fQuiet ^= 1;
            break;
        case 'v':
            fPrintTree ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    pNtk = Abc_FrameReadNtk(pAbc);

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

    pNtk = Abc_NtkDup( pNtk );
    Abc_NtkOrderObjsByName( pNtk, 1 );

    if (fOutputsOneAtTime) {
        int i;
        Abc_Obj_t * pNodePo;
        FILE * hadi = fopen("hadi.txt", "w");
        Abc_NtkForEachPo( pNtk, pNodePo, i ) {
            printf("Output %s\n\n", Abc_ObjName(pNodePo));
            saucyGateWay( pNtk, pNodePo, gFile, 0, fLookForSwaps, fFixOutputs, fFixInputs, fQuiet, fPrintTree );
            printf("----------------------------------------\n");
        }
        fclose(hadi);
    } else if (outputName != NULL) {
        int i;
        Abc_Obj_t * pNodePo;
        Abc_NtkForEachPo( pNtk, pNodePo, i ) {
            if (!strcmp(Abc_ObjName(pNodePo), outputName)) {
                saucyGateWay( pNtk, pNodePo, gFile, 0, fLookForSwaps, fFixOutputs, fFixInputs, fQuiet, fPrintTree );
                Abc_NtkDelete( pNtk );
                return 0;
            }
        }
        Abc_Print( -1, "Output not found\n" );
        return 1;
    } else
        saucyGateWay( pNtk, NULL, gFile, 0, fLookForSwaps, fFixOutputs, fFixInputs, fQuiet, fPrintTree );

    if (gFile != NULL) fclose(gFile);
    Abc_NtkDelete( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: saucy3 [-O <name>] [-F <file>] [-iosqvh]\n\n" );
    Abc_Print( -2, "\t            computes functional symmetries of the network\n" );
    Abc_Print( -2, "\t            prints symmetry generators to the standard output\n" );
    Abc_Print( -2, "\t-O <name> : (optional) compute symmetries only for output given by name\n");
    Abc_Print( -2, "\t            only inputs in the output cone are permuted\n");
    Abc_Print( -2, "\t            (special case) name=all, compute symmetries for each\n" );
    Abc_Print( -2, "\t            output, but only one output at a time\n" );
    Abc_Print( -2, "\t            [default = compute symmetries by permuting all I/Os]\n" );
    Abc_Print( -2, "\t-F <file> : print symmetry generators to file [default = stdout]\n");
    Abc_Print( -2, "\t-i        : permute just the inputs (fix the outputs) [default = no]\n");
    Abc_Print( -2, "\t-o        : permute just the outputs (fix the inputs) [default = no]\n");
    Abc_Print( -2, "\t-s        : only look for swaps of inputs [default = no]\n");
    Abc_Print( -2, "\t-q        : quiet (do not print symmetry generators) [default = no]\n");
    Abc_Print( -2, "\t-v        : verbose (print the search tree) [default = no]\n");
    Abc_Print( -2, "\t-h        : print the command usage\n");

    Abc_Print( -2, "\t            \n" );
    Abc_Print( -2, "\t            This command was contributed by Hadi Katebi from U Michigan.\n" );
    Abc_Print( -2, "\t            The paper describing the method: H. Katebi, K. Sakallah and\n");
    Abc_Print( -2, "\t            I. L. Markov.\n" );
    Abc_Print( -2, "\t            \"Generalized Boolean Symmetries Through Nested Partition\n");
    Abc_Print( -2, "\t            Refinement\". Proc. ICCAD 2013. \n" );
    //Abc_Print( -2, "\t          http://www.eecs.umich.edu/~imarkov/pubs/conf/date10-match.pdf\n" );
    Abc_Print( -2, "\t            Saucy webpage: http://vlsicad.eecs.umich.edu/BK/SAUCY/\n" );

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIso( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkNew = NULL;
    Aig_Man_t * pAig, * pTemp;
    Vec_Ptr_t * vPosEquivs = NULL;
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
    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        Abc_Print( 1, "Current AIG has only one PO. Transformation is not performed.\n");
        return 0;
    }

    // transform
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    pTemp = Saig_ManIsoReduce( pAig, &vPosEquivs, fVerbose );
    pNtkNew = Abc_NtkFromAigPhase( pTemp );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    Aig_ManStop( pTemp );
    Aig_ManStop( pAig );

    // update the internal storage of PO equivalences
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: iso [-vh]\n" );
    Abc_Print( -2, "\t         removes POs with isomorphic sequential COI\n" );
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
int Abc_CommandTraceStart( Abc_Frame_t * pAbc, int argc, char ** argv )
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
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command is applicable to AIGs.\n" );
        return 1;
    }
//    Abc_HManStart();
//    if ( !Abc_HManPopulate( pNtk ) )
//    {
//        Abc_Print( -1, "Failed to start the tracing database.\n" );
//        return 1;
//    }
    return 0;

usage:
    Abc_Print( -2, "usage: trace_start [-h]\n" );
    Abc_Print( -2, "\t        starts verification tracing\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
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
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command is applicable to AIGs.\n" );
        return 1;
    }
//    if ( !Abc_HManIsRunning(pNtk) )
//    {
//        Abc_Print( -1, "The tracing database is not available.\n" );
//        return 1;
//    }
//
//    if ( !Abc_HManVerify( 1, pNtk->Id ) )
//        Abc_Print( -1, "Verification failed.\n" );
//    Abc_HManStop();
    return 0;

usage:
    Abc_Print( -2, "usage: trace_check [-h]\n" );
    Abc_Print( -2, "\t        checks the current network using verification trace\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Miter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManPairWiseMiter( Gia_Man_t * p );
    extern Gia_Man_t * Gia_ManDupWithCare( Gia_Man_t * p, Gia_Man_t * pCare );
    FILE * pFile;
    Gia_Man_t * pAux;
    Gia_Man_t * pSecond;
    char * FileName, * pTemp;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int nInsDup  = 0;
    int fDualOut = 0;
    int fSeq     = 0;
    int fPairWise= 0;
    int fTrans   = 0;
    int fTransX  = 0;
    int fConvert = 0;
    int fTransZ  = 0;
    int fWithCare= 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Idsptxyzcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a char string.\n" );
                goto usage;
            }
            nInsDup = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsDup < 0 )
                goto usage;
            break;
        case 'd':
            fDualOut ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'p':
            fPairWise ^= 1;
            break;
        case 't':
            fTrans ^= 1;
            break;
        case 'x':
            fTransX ^= 1;
            break;
        case 'y':
            fConvert ^= 1;
            break;
        case 'z':
            fTransZ ^= 1;
            break;
        case 'c':
            fWithCare ^= 1;
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
    if ( fPairWise )
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Miter(): There is no AIG.\n" );
            return 1;
        }
        pAux = Gia_ManPairWiseMiter( pAbc->pGia );
        Abc_FrameUpdateGia( pAbc, pAux );
        return 0;
    }
    if ( fTrans || fTransX || fTransZ || fConvert )
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Miter(): There is no AIG.\n" );
            return 1;
        }
        if ( (Gia_ManPoNum(pAbc->pGia) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Miter(): The number of outputs should be even.\n" );
            return 0;
        }
        if ( fTrans )
        {
            pAux = Gia_ManTransformMiter( pAbc->pGia );
            Abc_Print( 1, "The miter (current AIG) is transformed by XORing POs pair-wise.\n" );
        }
        else if ( fTransX )
        {
            pAux = Gia_ManTransformMiter2( pAbc->pGia );
            Abc_Print( 1, "The miter (current AIG) is transformed by XORing POs of two word-level outputs.\n" );
        }
        else if ( fTransZ ) 
        {
            extern Gia_Man_t * Gia_ManTransformDualOutput( Gia_Man_t * p );
            pAux = Gia_ManTransformDualOutput( pAbc->pGia );
            Abc_Print( 1, "The dual-output miter (current AIG) is transformed by ordering sides.\n" );
        }
        else
        {
            pAux = Gia_ManTransformTwoWord2DualOutput( pAbc->pGia );
            Abc_Print( 1, "The miter (current AIG) is transformed from two-word to dual-output.\n" );
        }
        Abc_FrameUpdateGia( pAbc, pAux );
        return 0;
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
    // compute the miter
    if ( fWithCare )
        pAux = Gia_ManDupWithCare( pAbc->pGia, pSecond );
    else
        pAux = Gia_ManMiter( pAbc->pGia, pSecond, nInsDup, fDualOut, fSeq, 0, fVerbose );
    Gia_ManStop( pSecond );
    Abc_FrameUpdateGia( pAbc, pAux );
    return 0;

usage:
    Abc_Print( -2, "usage: &miter [-I num] [-dsptxyzcvh] <file>\n" );
    Abc_Print( -2, "\t         creates miter of two designs (current AIG vs. <file>)\n" );
    Abc_Print( -2, "\t-I num : the number of last PIs to replicate [default = %d]\n", nInsDup );
    Abc_Print( -2, "\t-d     : toggle creating dual-output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle creating sequential miter [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle creating pair-wise miter [default = %s]\n", fPairWise? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle XORing POs of dual-output miter [default = %s]\n", fTrans? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle XORing POs of two-word miter [default = %s]\n", fTransX? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle convering two-word miter into dual-output miter [default = %s]\n", fConvert? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle ordering sides of the dual-output miter [default = %s]\n", fTransZ? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle duplicating AIG with the care set [default = %s]\n", fWithCare? "yes": "no" );
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
int Abc_CommandAbc9Miter2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Gia_Man_t * pAux;
    char * FileName, * pTemp, * pInit;
    char ** pArgvNew;
    int nArgcNew;
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
    // extract string
    pInit = Extra_FileReadContents( FileName );
    Extra_StringClean( pInit, "01xX" );
    if ( (int)strlen(pInit) != Gia_ManCiNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Init string length (%d) differs from PI and flop count (%d).\n", strlen(pInit), Gia_ManCiNum(pAbc->pGia) );
        ABC_FREE( pInit );
        return 1;
    }
    // compute the miter
    pAux = Gia_ManMiter2( pAbc->pGia, pInit, fVerbose );
    ABC_FREE( pInit );
    Abc_FrameUpdateGia( pAbc, pAux );
    return 0;

usage:
    Abc_Print( -2, "usage: &miter2 [-vh] <file>\n" );
    Abc_Print( -2, "\t         creates miter of two copies of the design\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name with flop initial values (0/1/x/X) [default = required]\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Abc_ReadAigerOrVerilogFile( char * pFileName, char * pFileName2, char * pTopModule,
    Vec_Ptr_t * vDefines, Vec_Ptr_t * vBoxes, Vec_Ptr_t * vInsts, int Abstractions,
    Vec_Int_t * vDescriptor, int * pStatus )
{
    Gia_Man_t * pGia;
    *pStatus = 1;
    if ( !pFileName ) return NULL;
    if ( Sn_IsHdlFile(pFileName) )
    {
        Sn_GiaOptions_t GiaOptions;
        char * Files[2] = {pFileName, pFileName2};
        sn_module_id_t Top;
        sn_design_t * pDesign;
        memset(&GiaOptions, 0, sizeof(GiaOptions));
        GiaOptions.Blast = sn_blast_default_options();
        GiaOptions.vModules = vBoxes;
        GiaOptions.vInstances = vInsts;
        GiaOptions.fMemory = (Abstractions & 1) != 0;
        GiaOptions.fMultiply = (Abstractions & 2) != 0;
        pDesign = Sn_ReadVerifyHdl(pFileName2 ? 2 : 1, Files, pTopModule, vDefines, &Top,
                                  Abc_FrameReadErr(Abc_FrameGetGlobalFrame()));
        if ( !pDesign ) return NULL;
        pGia = Sn_DesignExtractGia(pDesign, Top, &GiaOptions, vDescriptor,
                                   Abc_FrameReadErr(Abc_FrameGetGlobalFrame()));
        sn_design_destroy(pDesign);
        if ( !pGia ) return NULL;
        ABC_FREE(pGia->pSpec);
        pGia->pSpec = Abc_UtilStrsav(pFileName);
    }
    else
    {
        FILE * pFile = fopen(pFileName, "rb");
        if ( !pFile )
        {
            Abc_Print(-1, "Cannot open input file \"%s\".\n", pFileName);
            char * pSimilar = Extra_FileGetSimilarName(pFileName, (char *)".aig", (char *)".aiger", NULL, NULL, NULL);
            if (pSimilar) Abc_Print(1, "Did you mean \"%s\"?\n", pSimilar);
            return NULL;
        }
        fclose(pFile);
        pGia = Gia_AigerRead(pFileName, 0, 0, 0);
    }
    if ( pGia ) *pStatus = 0;
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if all outputs of the swept miter are constant 0.]

  Description [The equivalence check below concludes from the swept miter
  having no AND nodes.  An AND-free GIA can still have outputs that are
  constant 1 or CI literals, which are satisfiable, so the outputs are
  checked here as well.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_CecSweptMiterIsConst0( Gia_Man_t * p )
{
    int i;
    for ( i = 0; i < Gia_ManPoNum(p); i++ )
        if ( !Gia_ManPoIsConst0(p, i) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Cec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Cec_ManPrintCexSummary( Gia_Man_t * p, Abc_Cex_t * pCex, Cec_ParCec_t * pPars );
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    FILE * pFile;
    Gia_Man_t * pGias[2] = {NULL, NULL}, * pMiter;
    char ** pArgvNew, * pTopModule = NULL, * pFileName2 = NULL;
    Vec_Ptr_t * vDefines = Vec_PtrAlloc( 0 );
    Vec_Ptr_t * vBoxes   = Vec_PtrAlloc( 0 );
    Vec_Ptr_t * vInsts   = Vec_PtrAlloc( 0 );
    int c, nArgcNew, fUseSim = 0, fUseNewX = 0, fUseNewY = 0, fMiter = 0, fDualOutput = 0, fDumpMiter = 0, fSavedSpec = 0;
    int Abc_ReadAigerOrVerilogFileStatus = 0, Abstractions = 0;
    Vec_Int_t * vDescriptors[2] = {Vec_IntAlloc(16), Vec_IntAlloc(16)};
    Cec_ManCecSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ACTMDIBFnmdbasxytvwh" ) ) != EOF )
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
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a file name.\n" );
                goto usage;
            }
            pTopModule = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by defines.\n" );
                goto usage;
            }
            Vec_PtrPush( vDefines, argv[globalUtilOptind] );
            globalUtilOptind++;
            break;
        case 'A':
            if ( globalUtilOptind >= argc ) goto usage;
            if ( !strcmp(argv[globalUtilOptind], "mem") ) Abstractions |= 1;
            else if ( !strcmp(argv[globalUtilOptind], "mul") ) Abstractions |= 2;
            else { Abc_Print(-1, "Unknown abstraction kind; use -A mem or -A mul.\n"); goto usage; }
            globalUtilOptind++;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by a module name.\n" );
                goto usage;
            }
            Vec_PtrPush( vBoxes, argv[globalUtilOptind] );
            globalUtilOptind++;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a top/instance path.\n" );
                goto usage;
            }
            Vec_PtrPush( vInsts, argv[globalUtilOptind] );
            globalUtilOptind++;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileName2 = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'n':
            pPars->fNaive ^= 1;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'd':
            fDualOutput ^= 1;
            break;
        case 'b':
            fSavedSpec ^= 1;
            break;
        case 'a':
            fDumpMiter ^= 1;
            break;
        case 's':
            pPars->fSilent ^= 1;
            break;
        case 'x':
            fUseNewX ^= 1;
            break;
        case 'y':
            fUseNewY ^= 1;
            break;
        case 't':
            fUseSim ^= 1;
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
    if ( pAbc->pGia && pAbc->pGia->nXors )
    {
        Abc_Print( 0, "It looks like the current AIG is derived by &st -m.  Such AIG contains XOR gates and cannot be verified before &st is applied.\n" );
        Vec_PtrFree( vDefines );
        Vec_PtrFree( vBoxes );
        Vec_PtrFree( vInsts );
        Vec_IntFree(vDescriptors[0]);
        Vec_IntFree(vDescriptors[1]);
        return 1;
    }
    if ( pFileName2 )
    {
        if ( (pFile = fopen( pFileName2, "r" )) == NULL )
        {
            Abc_Print( -1, "Cannot open input file \"%s\".\n", pFileName2 );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 1;
        }
        fclose( pFile );
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( fMiter )
    {
        if ( pAbc->pGia == NULL || nArgcNew != 0 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cec(): A miter cannot be given as an argument of command &cec and should be entered using &r.\n" );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 1;
        }
        if ( fDualOutput )
        {
            if ( Gia_ManPoNum(pAbc->pGia) & 1 )
            {
                Abc_Print( -1, "The dual-output miter should have an even number of outputs.\n" );
                Vec_PtrFree( vDefines );
                Vec_PtrFree( vBoxes );
                Vec_PtrFree( vInsts );
                Vec_IntFree(vDescriptors[0]);
                Vec_IntFree(vDescriptors[1]);
                return 1;
            }
            if ( !pPars->fSilent )
            Abc_Print( 1, "Assuming the current network is a double-output miter.\n" );
            pAbc->Status = Cec_ManVerify( pAbc->pGia, pPars );
        }
        else
        {
            abctime clk = Abc_Clock();
            Gia_Obj_t * pObj; int i;
            if ( !pPars->fSilent )
            Abc_Print( 1, "Assuming the current network is a single-output miter.\n" );
            if ( fUseSim )
            {
                abctime clk = Abc_Clock();
                extern int Gia_ManCheckSimEquiv( Gia_Man_t * p, int fVerbose );
                int Status = Gia_ManCheckSimEquiv( pAbc->pGia, pPars->fVerbose );
                if ( Status == 1 )
                    Abc_Print( 1, "Networks are equivalent.  " );
                else if ( Status == 0 )
                    Abc_Print( 1, "Networks are NOT equivalent.  " );
                else
                    Abc_Print( 1, "Networks are UNDECIDED.  " );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
                Vec_PtrFree( vDefines );
                Vec_PtrFree( vBoxes );
                Vec_PtrFree( vInsts );
                Vec_IntFree(vDescriptors[0]);
                Vec_IntFree(vDescriptors[1]);
                return 0;
            }
            // handle the case when the output is disproved by an all-0 primary input pattern
            ABC_FREE( pAbc->pGia->pCexComb );
            Gia_ManSetPhase( pAbc->pGia );
            Gia_ManForEachCo( pAbc->pGia, pObj, i )
                if ( pObj->fPhase )
                {
                    pAbc->pGia->pCexComb = Abc_CexAlloc( 0, Gia_ManCiNum(pAbc->pGia), 1 );
                    if ( !pPars->fSilent )
                    {
                        Abc_Print( 1, "Networks are NOT EQUIVALENT. Output %d trivially differs (different phase).  ", i );
                        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
                    }
                    pAbc->Status = 0;// satisfiable
                    break;
                }
            if ( pAbc->pGia->pCexComb == NULL )
            {
                Gia_Man_t * pTemp = Gia_ManDemiterToDual( pAbc->pGia );
                pAbc->Status = Cec_ManVerify( pTemp, pPars );
                ABC_SWAP( Abc_Cex_t *, pAbc->pGia->pCexComb, pTemp->pCexComb );
                Gia_ManStop( pTemp );
            }
        }
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexComb );
        Vec_PtrFree( vDefines );
        Vec_PtrFree( vBoxes );
        Vec_PtrFree( vInsts );
        Vec_IntFree(vDescriptors[0]);
        Vec_IntFree(vDescriptors[1]);
        return 0;
    }
    if ( nArgcNew > 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Cec(): Wrong number of command-line arguments.\n" );
        Vec_PtrFree( vDefines );
        Vec_PtrFree( vBoxes );
        Vec_PtrFree( vInsts );
        Vec_IntFree(vDescriptors[0]);
        Vec_IntFree(vDescriptors[1]);
        return 1;
    }
    if ( nArgcNew == 2 )
    {
        char * pFileNames[2] = { pArgvNew[0], pArgvNew[1] };
        int n;
        for ( n = 0; n < 2; n++ )
        {
            pGias[n] = Abc_ReadAigerOrVerilogFile( pFileNames[n], pFileName2, pTopModule, vDefines, vBoxes, vInsts, Abstractions, vDescriptors[n], &Abc_ReadAigerOrVerilogFileStatus );
            if ( pGias[n] == NULL )
            {
                if ( n ) Gia_ManStop(pGias[0]);
                Vec_PtrFree( vDefines );
                Vec_PtrFree( vBoxes );
                Vec_PtrFree( vInsts );
                Vec_IntFree(vDescriptors[0]);
                Vec_IntFree(vDescriptors[1]);
                return Abc_ReadAigerOrVerilogFileStatus;
            }
        }
    }
    else if ( fSavedSpec )
    {
        if ( pAbc->pGiaSaved == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cec(): There is no saved specification.\n" );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 1;
        }
        pGias[0] = pAbc->pGia;
        pGias[1] = pAbc->pGiaSaved;
    }
    else
    {
        char * FileName;
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cec(): There is no current AIG.\n" );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 1;
        }
        pGias[0] = pAbc->pGia;
        if ( nArgcNew == 1 )
            FileName = pArgvNew[0];
        else
        {
            assert( nArgcNew == 0 );
            if ( pAbc->pGia->pSpec == NULL )
            {
                Abc_Print( -1, "File name is not given on the command line.\n" );
                Vec_PtrFree( vDefines );
                Vec_PtrFree( vBoxes );
                Vec_PtrFree( vInsts );
                Vec_IntFree(vDescriptors[0]);
                Vec_IntFree(vDescriptors[1]);
                return 1;
            }
            FileName = pAbc->pGia->pSpec;
        }
        if ( fUseSim && nArgcNew == 1 && !strcmp( Extra_FileNameExtension(FileName), "truth" ) )
        {
            abctime clk = Abc_Clock();
            int Status = Gia_ManVerifyTruthFile( pGias[0], FileName, pPars->fVerbose );
            if ( Status == 1 )
                Abc_Print( 1, "Network and truth table are equivalent.  " );
            else if ( Status == 0 )
                Abc_Print( 1, "Network and truth table are NOT equivalent.  " );
            else
            {
                Vec_PtrFree( vDefines );
                Vec_PtrFree( vBoxes );
                Vec_PtrFree( vInsts );
                Vec_IntFree(vDescriptors[0]);
                Vec_IntFree(vDescriptors[1]);
                return 1;
            }
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            pAbc->Status = Status;
            Abc_FrameReplaceCex( pAbc, &pGias[0]->pCexComb );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 0;
        }
        pGias[1] = Abc_ReadAigerOrVerilogFile( FileName, pFileName2, pTopModule, vDefines, vBoxes, vInsts, Abstractions, vDescriptors[1], &Abc_ReadAigerOrVerilogFileStatus );
        if ( pGias[1] == NULL )
        {
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return Abc_ReadAigerOrVerilogFileStatus;
        }
    }
    if (pGias[0] == pAbc->pGia && !Vec_IntSize(vDescriptors[0]))
    {
        const Vec_Int_t * vSaved = Sn_CurrentGiaDescriptor(pAbc, pGias[0]);
        if (vSaved) Vec_IntAppend(vDescriptors[0], (Vec_Int_t *)vSaved);
    }
    if ( Gia_ManRegNum(pGias[0]) != Gia_ManRegNum(pGias[1]) ||
         Gia_ManPiNum(pGias[0]) != Gia_ManPiNum(pGias[1]) ||
         Gia_ManPoNum(pGias[0]) != Gia_ManPoNum(pGias[1]) ||
         (Vec_IntSize(vDescriptors[0]) && Vec_IntSize(vDescriptors[1]) &&
          !Vec_IntEqual(vDescriptors[0], vDescriptors[1])) ||
         ((Abstractions || Vec_PtrSize(vBoxes) || Vec_PtrSize(vInsts)) &&
          (!Vec_IntSize(vDescriptors[0]) || !Vec_IntSize(vDescriptors[1]))) )
    {
        if (Gia_ManPiNum(pGias[0]) != Gia_ManPiNum(pGias[1]))
            Abc_Print(-1, "Incompatible PI counts: %d versus %d.\n", Gia_ManPiNum(pGias[0]), Gia_ManPiNum(pGias[1]));
        if (Gia_ManPoNum(pGias[0]) != Gia_ManPoNum(pGias[1]))
            Abc_Print(-1, "Incompatible PO counts: %d versus %d.\n", Gia_ManPoNum(pGias[0]), Gia_ManPoNum(pGias[1]));
        if (Gia_ManRegNum(pGias[0]) != Gia_ManRegNum(pGias[1]))
            Abc_Print(-1, "Incompatible flop counts: %d versus %d; preserved flops are required.\n",
                Gia_ManRegNum(pGias[0]), Gia_ManRegNum(pGias[1]));
        if (Vec_IntSize(vDescriptors[0]) && Vec_IntSize(vDescriptors[1]) &&
            !Vec_IntEqual(vDescriptors[0], vDescriptors[1]))
            Abc_Print(-1, "Incompatible positional cut descriptors.\n");
        if ((Abstractions || Vec_PtrSize(vBoxes) || Vec_PtrSize(vInsts)) &&
            (!Vec_IntSize(vDescriptors[0]) || !Vec_IntSize(vDescriptors[1])))
            Abc_Print(-1, "Cut comparison requires a valid extraction descriptor on both sides; "
                "an AIG load or replacement invalidates the saved descriptor.\n");
        Abc_Print(-1, "Comparison not performed.\n");
        for ( int i = 0; i < 2; ++i )
            if ( pGias[i] != pAbc->pGia && pGias[i] != pAbc->pGiaSaved ) Gia_ManStop(pGias[i]);
        Vec_PtrFree(vDefines); Vec_PtrFree(vBoxes); Vec_PtrFree(vInsts);
        Vec_IntFree(vDescriptors[0]); Vec_IntFree(vDescriptors[1]);
        return 1;
    }
    if ( Abstractions || Vec_PtrSize(vBoxes) || Vec_PtrSize(vInsts) )
        Abc_Print(1, "CEC is conditional on the shared abstract box outputs; removed internals are not verified.\n");
    pPars->pNameSpec = pGias[0] ? (pGias[0]->pSpec ? pGias[0]->pSpec : pGias[0]->pName) : NULL;
    pPars->pNameImpl = pGias[1] ? (pGias[1]->pSpec ? pGias[1]->pSpec : pGias[1]->pName) : NULL;
    pPars->vNamesIn  = pGias[0] ? pGias[0]->vNamesIn : NULL;
    // compute the miter
    if ( Gia_ManCiNum(pGias[0]) < 6 )
    {
        Gia_Man_t * pGias0 = Gia_ManDup( pGias[0] );
        Gia_Man_t * pGias1 = Gia_ManDup( pGias[1] );
        for ( c = Gia_ManCiNum(pGias[0]); c < 6; c++ )
        {
            Gia_ManAppendCi(pGias0);
            Gia_ManAppendCi(pGias1);
        }
        pMiter = Gia_ManMiter( pGias0, pGias1, 0, !fUseNewX && !fUseNewY, 0, 0, pPars->fVerbose );
        Gia_ManStop( pGias0 );
        Gia_ManStop( pGias1 );
    }
    else
        pMiter = Gia_ManMiter( pGias[0], pGias[1], 0, !fUseNewX && !fUseNewY, 0, 0, pPars->fVerbose );

    if ( pMiter )
    {
        if ( fDumpMiter )
        {
            Abc_Print( 0, "The verification miter is written into file \"%s\".\n", "cec_miter.aig" );
            Gia_AigerWrite( pMiter, "cec_miter.aig", 0, 0, 0 );
        }
        if ( pGias[0]->vSimsPi )
        {
            pMiter->vSimsPi = Vec_WrdDup(pGias[0]->vSimsPi); 
            pMiter->nSimWords = pGias[0]->nSimWords;
        }
        if ( fUseSim && Gia_ManCiNum(pMiter) > 40 )
        {
            Abc_Print( -1, "This type of CEC can only be applied to AIGs with no more than 40 inputs.\n" );
            Vec_PtrFree( vDefines );
            Vec_PtrFree( vBoxes );
            Vec_PtrFree( vInsts );
            Vec_IntFree(vDescriptors[0]);
            Vec_IntFree(vDescriptors[1]);
            return 0;
        }
        if ( fUseSim )
        {
            abctime clk = Abc_Clock();
            extern int Gia_ManCheckSimEquiv( Gia_Man_t * p, int fVerbose );
            int Status = Gia_ManCheckSimEquiv( pMiter, pPars->fVerbose );
            if ( Status == 1 )
            {
                Abc_Print( 1, "Networks are equivalent.  " );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            }
            else if ( Status == 0 )
            {
                Abc_Print( 1, "Networks are NOT equivalent.  " );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
                {
                    Cec_ParCec_t ParsTemp = *pPars;
                    ParsTemp.fSilent = 1;
                    Cec_ManVerify( pMiter, &ParsTemp );
                    if ( pMiter->pCexComb )
                    {
                        Cec_ManPrintCexSummary( pMiter, pMiter->pCexComb, pPars );
                        pGias[0]->pCexComb = pMiter->pCexComb; 
                        pMiter->pCexComb = NULL;
                        Abc_FrameReplaceCex( pAbc, &pGias[0]->pCexComb );
                    }
                }
            }
            else
            {
                Abc_Print( 1, "Networks are UNDECIDED.  " );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            }
        }
        else if ( fUseNewX )
        {
            abctime clk = Abc_Clock();
            extern Gia_Man_t * Cec4_ManSimulateTest3( Gia_Man_t * p, int nBTLimit, int fVerbose );
            Gia_Man_t * pNew = Cec4_ManSimulateTest3( pMiter, pPars->nBTLimit, pPars->fVerbose );
            if ( Gia_ManAndNum(pNew) != 0 )
                Abc_Print( 1, "Networks are UNDECIDED.  " );
            else if ( Abc_CecSweptMiterIsConst0(pNew) )
                Abc_Print( 1, "Networks are equivalent.  " );
            else
                Abc_Print( 1, "Networks are NOT equivalent.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            Gia_ManStop( pNew );
        }
        else if ( fUseNewY )
        {
            abctime clk = Abc_Clock();
            extern Gia_Man_t * Cec5_ManSimulateTest3( Gia_Man_t * p, int nBTLimit, int fVerbose );
            Gia_Man_t * pNew = Cec5_ManSimulateTest3( pMiter, pPars->nBTLimit, pPars->fVerbose );
            if ( Gia_ManAndNum(pNew) != 0 )
                Abc_Print( 1, "Networks are UNDECIDED.  " );
            else if ( Abc_CecSweptMiterIsConst0(pNew) )
                Abc_Print( 1, "Networks are equivalent.  " );
            else
                Abc_Print( 1, "Networks are NOT equivalent.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            Gia_ManStop( pNew );
        }
        else
        {
            pAbc->Status = Cec_ManVerify( pMiter, pPars );
            Abc_FrameReplaceCex( pAbc, &pGias[0]->pCexComb );
        }
        Gia_ManStop( pMiter );
    }
    if ( pGias[0] != pAbc->pGia )
        Gia_ManStop( pGias[0] );
    if ( pGias[1] != pAbc->pGiaSaved )
        Gia_ManStop( pGias[1] );
    Vec_PtrFree( vDefines );
    Vec_PtrFree( vBoxes );
    Vec_PtrFree( vInsts );
    Vec_IntFree(vDescriptors[0]);
    Vec_IntFree(vDescriptors[1]);
    return 0;

usage:
    Abc_Print( -2, "usage: &cec [-CT num] [-M str] [-D str] [-B str] [-I str] [-A kind] [-F str] [-nmdbasxytvwh]\n" );
    Abc_Print( -2, "\t         new combinational equivalence checker\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-M str : top module name for HDL inputs [default = inferred]\n" );
    Abc_Print( -2, "\t-A kind: abstract inferred mem or mul operators (repeatable)\n" );
    Abc_Print( -2, "\t-D str : macro definition for HDL inputs (repeatable) [default = none]\n" );
    Abc_Print( -2, "\t-B str : declared HDL module to abstract as a cut (repeatable) [default = none]\n" );
    Abc_Print( -2, "\t-I str : exact instance path, rooted at or relative to the top (repeatable)\n" );
    Abc_Print( -2, "\t-F str : additional HDL file read with each HDL operand [default = none]\n" );
    Abc_Print( -2, "\t-n     : toggle using naive SAT-based checking [default = %s]\n", pPars->fNaive? "yes":"no");
    Abc_Print( -2, "\t-m     : toggle miter vs. two circuits [default = %s]\n", fMiter? "miter":"two circuits");
    Abc_Print( -2, "\t-d     : toggle using dual output miter [default = %s]\n", fDualOutput? "yes":"no");
    Abc_Print( -2, "\t-b     : toggle using saved specification [default = %s]\n", fSavedSpec? "yes":"no");
    Abc_Print( -2, "\t-a     : toggle writing dual-output miter [default = %s]\n", fDumpMiter? "yes":"no");
    Abc_Print( -2, "\t-s     : toggle silent operation [default = %s]\n", pPars->fSilent ? "yes":"no");
    Abc_Print( -2, "\t-x     : toggle using new solver [default = %s]\n", fUseNewX? "yes":"no");
    Abc_Print( -2, "\t-y     : toggle using new solver [default = %s]\n", fUseNewY? "yes":"no");
    Abc_Print( -2, "\t-t     : toggle using simulation; accepts one .truth file for the current network [default = %s]\n", fUseSim? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-w     : toggle printing SAT solver statistics [default = %s]\n", pPars->fVeryVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tInterfaces match positionally, never by name; PI/PO/flop counts must agree.\n" );
    Abc_Print( -2, "\tFlops must be preserved; this is combinational, not sequential equivalence.\n" );
    Abc_Print( -2, "\tCut proofs are conditional on aligned abstract outputs, not proof of removed internals.\n" );
    Abc_Print( -2, "\t-F may require -M if the additional source introduces another top module.\n" );
    Vec_PtrFree( vDefines );
    Vec_PtrFree( vBoxes );
    Vec_PtrFree( vInsts );
    Vec_IntFree(vDescriptors[0]);
    Vec_IntFree(vDescriptors[1]);
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ICec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    FILE * pFile;
    Gia_Man_t * pGias[2] = {NULL, NULL}, * pMiter;
    char ** pArgvNew;
    int c, nArgcNew, fUseNew = 0, fDumpMiter = 0;
    Cec_ManCecSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTaxvwh" ) ) != EOF )
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
        case 'a':
            fDumpMiter ^= 1;
            break;
        case 'x':
            fUseNew ^= 1;
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
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew > 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Cec(): Wrong number of command-line arguments.\n" );
        return 1;
    }
    if ( nArgcNew == 2 )
    {
        char * pFileNames[2] = { pArgvNew[0], pArgvNew[1] }, * pTemp;
        int n;
        for ( n = 0; n < 2; n++ )
        {
            // fix the wrong symbol
            for ( pTemp = pFileNames[n]; *pTemp; pTemp++ )
                if ( *pTemp == '>' )
                    *pTemp = '\\';
            if ( (pFile = fopen( pFileNames[n], "r" )) == NULL )
            {
                Abc_Print( -1, "Cannot open input file \"%s\". ", pFileNames[n] );
                if ( (pFileNames[n] = Extra_FileGetSimilarName( pFileNames[n], ".aig", NULL, NULL, NULL, NULL )) )
                    Abc_Print( 1, "Did you mean \"%s\"?", pFileNames[n] );
                Abc_Print( 1, "\n" );
                return 1;
            }
            fclose( pFile );
            pGias[n] = Gia_AigerRead( pFileNames[n], 0, 0, 0 );
            if ( pGias[n] == NULL )
            {
                Abc_Print( -1, "Reading AIGER from file \"%s\" has failed.\n", pFileNames[n] );
                return 0;
            }
        }
    }
    else
    {
        char * FileName, * pTemp;
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Cec(): There is no current AIG.\n" );
            return 1;
        }
        pGias[0] = pAbc->pGia;
        if ( nArgcNew == 1 )
            FileName = pArgvNew[0];
        else
        {
            assert( nArgcNew == 0 );
            if ( pAbc->pGia->pSpec == NULL )
            {
                Abc_Print( -1, "File name is not given on the command line.\n" );
                return 1;
            }
            FileName = pAbc->pGia->pSpec;
        }
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
        pGias[1] = Gia_AigerRead( FileName, 0, 0, 0 );
        if ( pGias[1] == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 0;
        }
    }
    // compute the miter
    pMiter = Gia_ManMiterInverse( pGias[0], pGias[1], !fUseNew, pPars->fVerbose );
    if ( pMiter )
    {
        if ( fDumpMiter )
        {
            Abc_Print( 0, "The verification miter is written into file \"%s\".\n", "cec_miter.aig" );
            Gia_AigerWrite( pMiter, "cec_miter.aig", 0, 0, 0 );
        }
        if ( fUseNew )
        {
            abctime clk = Abc_Clock();
            extern Gia_Man_t * Cec4_ManSimulateTest3( Gia_Man_t * p, int nBTLimit, int fVerbose );
            Gia_Man_t * pNew = Cec4_ManSimulateTest3( pMiter, pPars->nBTLimit, pPars->fVerbose );
            if ( Gia_ManAndNum(pNew) != 0 )
                Abc_Print( 1, "Networks are UNDECIDED.  " );
            else if ( Abc_CecSweptMiterIsConst0(pNew) )
                Abc_Print( 1, "Networks are equivalent.  " );
            else
                Abc_Print( 1, "Networks are NOT equivalent.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            Gia_ManStop( pNew );
        }
        else
        {
            pAbc->Status = Cec_ManVerify( pMiter, pPars );
            Abc_FrameReplaceCex( pAbc, &pGias[0]->pCexComb );
        }
        Gia_ManStop( pMiter );
    }
    if ( pGias[0] != pAbc->pGia )
        Gia_ManStop( pGias[0] );
    Gia_ManStop( pGias[1] );
    return 0;

usage:
    Abc_Print( -2, "usage: &icec [-CT num] [-axvwh]\n" );
    Abc_Print( -2, "\t         combinational equivalence checker for inverse circuits\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-a     : toggle writing the miter [default = %s]\n", fDumpMiter? "yes":"no");
    Abc_Print( -2, "\t-x     : toggle using new solver [default = %s]\n", fUseNew? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-w     : toggle printing SAT solver statistics [default = %s]\n", pPars->fVeryVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Verify( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileSpec = NULL;
    int c, nBTLimit = 1000, nTimeLim = 0, fSeq = 0, fObjIdMap = 0, fDumpFiles = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTsydvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeLim < 0 )
                goto usage;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'y':
            fObjIdMap ^= 1;
            break;
        case 'd':
            fDumpFiles ^= 1;
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
    if ( argc > globalUtilOptind + 1 )
        goto usage;
    if ( argc == globalUtilOptind + 1 )
    {
        pFileSpec = argv[globalUtilOptind];
        Extra_FileNameCorrectPath( pFileSpec );
        printf( "Taking spec from file \"%s\".\n", pFileSpec );
    }
    Abc_FrameSetStatus( Gia_ManVerifyWithBoxes(pAbc->pGia, nBTLimit, nTimeLim, fSeq, fObjIdMap, fDumpFiles, fVerbose, pFileSpec) );
    return 0;

usage:
    Abc_Print( -2, "usage: &verify [-CT num] [-sydvh] <file>\n" );
    Abc_Print( -2, "\t         performs verification of combinational design\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n",  nTimeLim );
    Abc_Print( -2, "\t-s     : toggle using sequential verification [default = %s]\n",  fSeq? "yes":"no");
    Abc_Print( -2, "\t-y     : toggle producing object ID mapping (CEC only) [default = %s]\n", fObjIdMap? "yes":"no");
    Abc_Print( -2, "\t-d     : toggle dumping AIGs to be compared [default = %s]\n",    fDumpFiles? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n",                 fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : optional file name with the spec [default = not used]\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Iso( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pAig;
    Vec_Ptr_t * vPosEquivs;
//    Vec_Ptr_t * vPiPerms;
    int c, fNewAlgo = 1, fEstimate = 0, fBetterQual = 0, fDualOut = 0, fVerbose = 0, fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "neqdvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fNewAlgo ^= 1;
            break;
        case 'e':
            fEstimate ^= 1;
            break;
        case 'q':
            fBetterQual ^= 1;
            break;
        case 'd':
            fDualOut ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Iso(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) == 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iso(): The AIG has only one PO. Isomorphism detection is not performed.\n" );
        return 1;
    }
    if ( fNewAlgo )
        pAig = Gia_ManIsoReduce2( pAbc->pGia, &vPosEquivs, NULL, fEstimate, fBetterQual, fDualOut, fVerbose, fVeryVerbose );
    else
        pAig = Gia_ManIsoReduce( pAbc->pGia, &vPosEquivs, NULL, fEstimate, fDualOut, fVerbose, fVeryVerbose );
//    pAig = Gia_ManIsoReduce( pAbc->pGia, &vPosEquivs, &vPiPerms, 0, fDualOut, fVerbose, fVeryVerbose );
//    Vec_VecFree( (Vec_Vec_t *)vPiPerms );
    if ( pAig == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Iso(): Transformation has failed.\n" );
        return 1;
    }
    // update the internal storage of PO equivalences
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );
    // update the AIG
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &iso [-neqdvwh]\n" );
    Abc_Print( -2, "\t         removes POs with isomorphic sequential COI\n" );
    Abc_Print( -2, "\t-n     : toggle using new fast algorithm [default = %s]\n", fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle computing lower bound on equivalence classes [default = %s]\n", fEstimate? "yes": "no" );
    Abc_Print( -2, "\t-q     : toggle improving quality at the expense of runtime [default = %s]\n", fBetterQual? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle treating the current AIG as a dual-output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9IsoNpn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManIsoNpnReduce( Gia_Man_t * p, Vec_Ptr_t ** pvPosEquivs, int fVerbose );
    Gia_Man_t * pAig;
    Vec_Ptr_t * vPosEquivs;
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
        Abc_Print( -1, "Abc_CommandAbc9IsoNpn(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) == 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoNpn(): The AIG has only one PO. Isomorphism detection is not performed.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoNpn(): ISO-NPN does not work with sequential AIGs.\n" );
        return 1;
    }
    pAig = Gia_ManIsoNpnReduce( pAbc->pGia, &vPosEquivs, fVerbose );
    if ( pAig == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoNpn(): Transformation has failed.\n" );
        return 1;
    }
    // update the internal storage of PO equivalences
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );
    // update the AIG
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &isonpn [-vh]\n" );
    Abc_Print( -2, "\t         removes POs with functionally isomorphic combinational COI\n" );
    Abc_Print( -2, "\t         (currently ignores POs whose structural support is more than 16)\n" );
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
int Abc_CommandAbc9IsoSt( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManIsoStrashReduce( Gia_Man_t * p, Vec_Ptr_t ** pvPosEquivs, int fVerbose );
    Gia_Man_t * pAig;
    Vec_Ptr_t * vPosEquivs;
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
        Abc_Print( -1, "Abc_CommandAbc9IsoSt(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) == 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoSt(): The AIG has only one PO. Isomorphism detection is not performed.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoSt(): ISO-ST does not work with sequential AIGs.\n" );
        return 1;
    }
    pAig = Gia_ManIsoStrashReduce( pAbc->pGia, &vPosEquivs, fVerbose );
    if ( pAig == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9IsoSt(): Transformation has failed.\n" );
        return 1;
    }
    // update the internal storage of PO equivalences
    Abc_FrameReplacePoEquivs( pAbc, &vPosEquivs );
    // update the AIG
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &isost [-vh]\n" );
    Abc_Print( -2, "\t         removes POs with functionally isomorphic combinational COI\n" );
    Abc_Print( -2, "\t         (this command relies exclusively on structural hashing)\n" );
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
int Abc_CommandAbc9Store( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fClean = 0, fPrint = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fClean ^= 1;
            break;
        case 'p':
            fPrint ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Store(): There is no AIG.\n" );
        return 1;
    }
    if ( fClean )
        Abc_FrameStoreStop( pAbc );
    else if ( fPrint )
        Abc_FrameStorePrint( pAbc );
    else
        Abc_FrameStoreAdd( pAbc, pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &store [-cpvh]\n" );
    Abc_Print( -2, "\t         maintains the store of unique AIG structures\n" );
    Abc_Print( -2, "\t-c     : toggle cleaning the store [default = %s]\n", fClean? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle printing the store statistics [default = %s]\n", fPrint? "yes": "no" );
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
int Abc_CommandAbc9Compare( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_Iso4TestTwo( Gia_Man_t * pGia0, Gia_Man_t * pGia1 );
    extern void Gia_ManComparePrint( Gia_Man_t * p, Gia_Man_t * q );
    Gia_Man_t * pGia0, * pGia1;
    char ** pArgvNew; int nArgcNew;
    int c, fFunc = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFunc ^= 1;
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
    if ( nArgcNew != 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Compare(): This command expects two AIG file names on the command line.\n" );
        return 1;
    }
    pGia0 = Gia_AigerRead( pArgvNew[0], 0, 0, 0 );
    pGia1 = Gia_AigerRead( pArgvNew[1], 0, 0, 0 );
    if ( pGia0 == NULL || pGia1 == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Compare(): Reading input files did not work.\n" );
        return 1;
    }
    if ( fFunc )
        Gia_ManComparePrint( pGia0, pGia1 );
    else
        Gia_Iso4TestTwo( pGia0, pGia1 );
    Gia_ManStop( pGia0 );
    Gia_ManStop( pGia1 );
    return 0;

usage:
    Abc_Print( -2, "usage: &compare <file1> <file2> [-fvh]\n" );
    Abc_Print( -2, "\t         compared two AIGs for structural similarity\n" );
    Abc_Print( -2, "\t-f     : toggle functional comparison [default = %s]\n", fFunc? "yes": "no" );
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
int Abc_CommandAbc9RevEng( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManCompareSims( Gia_Man_t * pHie, Gia_Man_t * pFlat, int nWords, int fVerbose );
    Gia_Man_t * pGia0, * pGia1;
    char ** pArgvNew; int nArgcNew;
    int c, nWords = 4, fVerbose = 0;
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
            if ( nWords < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9RevEng(): There is no AIG.\n" );
        return 1;
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9RevEng(): This command expects one AIG file name on the command line.\n" );
        return 1;
    }
    pGia0 = pAbc->pGia;
    pGia1 = Gia_AigerRead( pArgvNew[0], 0, 0, 0 );
    if ( pGia0 == NULL || pGia1 == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9RevEng(): Reading input files did not work.\n" );
        return 1;
    }
    Gia_ManCompareSims( pGia0, pGia1, nWords, fVerbose );
    Gia_ManStop( pGia1 );
    return 0;

usage:
    Abc_Print( -2, "usage: &reveng [-W num] [-vh] <file>\n" );
    Abc_Print( -2, "\t         compares two AIGs for structural similarity\n" );
    Abc_Print( -2, "\t         the current AIG is expected to contain some hierarchy\n" );
    Abc_Print( -2, "\t         the given AIG from <file> is expected to be flat\n" );
    Abc_Print( -2, "\t-W num : the number of 64-bit words of simulation info [default = %d]\n", nWords );
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
int Abc_CommandAbc9SplitProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Cec_GiaSplitTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nIterMax, int LookAhead, int fVerbose, int fVeryVerbose, int fSilent );
    int c, nProcs = 1, nTimeOut = 10, nIterMax = 0, LookAhead = 1, fVerbose = 0, fVeryVerbose = 0, fSilent = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PTILsvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nProcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProcs <= 0 )
                goto usage;
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
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIterMax < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            LookAhead = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LookAhead <= 0 || LookAhead > 100 )
            {
                Abc_Print( -1, "Look-ahead value (\"-L <num>\") should be between 1 and 100.\n", LookAhead );
                goto usage;
            }
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
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SplitProve(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9SplitProve(): The problem is sequential.\n" );
        return 1;
    }
    pAbc->Status = Cec_GiaSplitTest( pAbc->pGia, nProcs, nTimeOut, nIterMax, LookAhead, fVerbose, fVeryVerbose, fSilent );
    pAbc->pCex = pAbc->pGia->pCexComb;  pAbc->pGia->pCexComb = NULL;
    return 0;

usage:
    Abc_Print( -2, "usage: &splitprove [-PTIL num] [-svwh]\n" );
    Abc_Print( -2, "\t         proves CEC problem by case-splitting\n" );
    Abc_Print( -2, "\t-P num : the number of concurrent processes [default = %d]\n",          nProcs );
    Abc_Print( -2, "\t-T num : runtime limit in seconds per subproblem [default = %d]\n",     nTimeOut );
    Abc_Print( -2, "\t-I num : the max number of iterations (0 = infinity) [default = %d]\n", nIterMax );
    Abc_Print( -2, "\t-L num : maximum look-ahead during cofactoring [default = %d]\n",       LookAhead );
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
int Abc_CommandAbc9Demiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fDumpFiles = 0, fDumpFilesTwo = 0, fDual = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ftdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fDumpFiles ^= 1;
            break;
        case 't':
            fDumpFilesTwo ^= 1;
            break;
        case 'd':
            fDual ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Demiter(): There is no AIG.\n" );
        return 0;
    }
    if ( fDumpFiles || fDumpFilesTwo )
    {
        char pName0[1000] = "miter_part0.aig";
        char pName1[1000] = "miter_part1.aig";
        Gia_Man_t * pPart1, * pPart2;
        if ( Gia_ManPoNum(pAbc->pGia) % 2 != 0 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Demiter(): Does not look like a dual-output miter.\n" );
            return 0;
        }
        if ( fDumpFilesTwo )
            Gia_ManDemiterTwoWords( pAbc->pGia, &pPart1, &pPart2 );
        else
            Gia_ManDemiterDual( pAbc->pGia, &pPart1, &pPart2 );
        if ( pAbc->pGia->pSpec )
        {
            char * pGen = Extra_FileNameGeneric(pAbc->pGia->pSpec);
            sprintf( pName0, "%s_1.aig", pGen );
            sprintf( pName1, "%s_2.aig", pGen );
            ABC_FREE( pGen );
        }
        Gia_AigerWrite( pPart1, pName0, 0, 0, 0 );
        Gia_AigerWrite( pPart2, pName1, 0, 0, 0 );
        Gia_ManStop( pPart1 );
        Gia_ManStop( pPart2 );
        if ( fDumpFilesTwo )
            printf( "Two parts of the two-word miter are dumped into files \"%s\" and \"%s\".\n", pName0, pName1 );
        else
            printf( "Two parts of the dual-output miter are dumped into files \"%s\" and \"%s\".\n", pName0, pName1 );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Demiter(): Miter should have one output.\n" );
        return 0;
    }
    if ( fDual )
        pTemp = Gia_ManDemiterToDual( pAbc->pGia );
    else
        pTemp = Gia_ManDupDemiter( pAbc->pGia, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    if ( fVerbose )
        Gia_ManPrintStatsMiter( pTemp, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: &demiter [-ftdvh]\n" );
    Abc_Print( -2, "\t         decomposes a miter (by default, tries to extract an OR gate)\n" );
    Abc_Print( -2, "\t-f     : write files with two sides of a dual-output miter [default = %s]\n",  fDumpFiles? "yes": "no" );
    Abc_Print( -2, "\t-t     : write files with two sides of a two-word miter [default = %s]\n",  fDumpFilesTwo? "yes": "no" );
    Abc_Print( -2, "\t-d     : take single-output and decompose into dual-output [default = %s]\n",  fDual? "yes": "no" );
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
int Abc_CommandAbc9Acec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Acec_ParCec_t ParsCec, * pPars = &ParsCec;
    char ** pArgvNew;
    int c, nArgcNew;
    Acec_ManCecSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTmdtbvh" ) ) != EOF )
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
        case 'm':
            pPars->fMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOutput ^= 1;
            break;
        case 't':
            pPars->fTwoOutput ^= 1;
            break;
        case 'b':
            pPars->fBooth ^= 1;
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
    if ( pPars->fMiter )
    {
        Gia_Man_t * pGia0, * pGia1, * pDual;
        if ( argc != globalUtilOptind )
        {
            Abc_Print( -1, "Abc_CommandAbc9Acec(): If the input is a miter, it cannot be given on the command line.\n" );
            return 1;
        }
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "Abc_CommandAbc9Acec(): There is no AIG.\n" );
            return 1;
        }
        if ( pPars->fDualOutput )
        {
            if ( Gia_ManPoNum(pAbc->pGia) & 1 )
            {
                Abc_Print( -1, "The dual-output miter should have an even number of outputs.\n" );
                return 1;
            }
            if ( !pPars->fSilent )
            Abc_Print( 1, "Assuming the current network is a double-output miter. (Conflict limit = %d.)\n", pPars->nBTLimit );
            Gia_ManDemiterDual( pAbc->pGia, &pGia0, &pGia1 );
            pAbc->Status = Acec_Solve( pGia0, pGia1, pPars );
        }
        else if ( pPars->fTwoOutput )
        {
            if ( Gia_ManPoNum(pAbc->pGia) & 1 )
            {
                Abc_Print( -1, "The two-output miter should have an even number of outputs.\n" );
                return 1;
            }
            if ( !pPars->fSilent )
            Abc_Print( 1, "Assuming the current network is a two-word miter. (Conflict limit = %d.)\n", pPars->nBTLimit );
            Gia_ManDemiterTwoWords( pAbc->pGia, &pGia0, &pGia1 );
            pAbc->Status = Acec_Solve( pGia0, pGia1, pPars );
        }
        else // regular single- or multi-output miter
        {
            if ( !pPars->fSilent )
            Abc_Print( 1, "Assuming the current network is a regular single- or multi-output miter. (Conflict limit = %d.)\n", pPars->nBTLimit );
            pDual = Gia_ManDemiterToDual( pAbc->pGia );
            Gia_ManDemiterDual( pDual, &pGia0, &pGia1 );
            Gia_ManStop( pDual );
            pAbc->Status = Acec_Solve( pGia0, pGia1, pPars );
        }
        Abc_FrameReplaceCex( pAbc, &pGia0->pCexComb );
        Gia_ManStop( pGia0 );
        Gia_ManStop( pGia1 );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew == 0 || nArgcNew == 1 )
    {
        Gia_Man_t * pSecond;
        char * pTemp, * FileName = NULL;
        if ( nArgcNew == 0 )
        {
            FileName = pAbc->pGia->pSpec;
            if ( FileName == NULL )
            {
                Abc_Print( -1, "File name is not given on the command line.\n" );
                return 1;
            }
        }
        else // if ( nArgcNew == 1 )
        {
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
        }
        pSecond = Gia_AigerRead( FileName, 0, 0, 0 );
        if ( pSecond == NULL )
        {
            Abc_Print( -1, "Reading AIGER has failed.\n" );
            return 0;
        }
        pAbc->Status = Acec_Solve( pAbc->pGia, pSecond, pPars );
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexComb );
        Gia_ManStop( pSecond );
    }
    else if ( nArgcNew == 2 )
    {
        Gia_Man_t * pGias[2] = {NULL};  int i;
        char * pTemp, * FileName[2] = { pArgvNew[0], pArgvNew[1] };
        for ( i = 0; i < 2; i++ )
        {
            // fix the wrong symbol
            for ( pTemp = FileName[i]; *pTemp; pTemp++ )
                if ( *pTemp == '>' )
                    *pTemp = '\\';
            if ( (pFile = fopen( FileName[i], "r" )) == NULL )
            {
                Abc_Print( -1, "Cannot open input file \"%s\". ", FileName[i] );
                if ( (FileName[i] = Extra_FileGetSimilarName( FileName[i], ".aig", NULL, NULL, NULL, NULL )) )
                    Abc_Print( 1, "Did you mean \"%s\"?", FileName[i] );
                Abc_Print( 1, "\n" );
                return 1;
            }
            fclose( pFile );
            pGias[i] = Gia_AigerRead( FileName[i], 0, 0, 0 );
            if ( pGias[i] == NULL )
            {
                Abc_Print( -1, "Reading AIGER has failed.\n" );
                return 0;
            }
        }
        pAbc->Status = Acec_Solve( pGias[0], pGias[1], pPars );
        Abc_FrameReplaceCex( pAbc, &pGias[0]->pCexComb );
        Gia_ManStop( pGias[0] );
        Gia_ManStop( pGias[1] );
    }
    else
    {
        Abc_Print( -1, "Too many command-line arguments.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &acec [-CT num] [-mdtbvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         combinational equivalence checking for arithmetic circuits\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. two circuits [default = %s]\n", pPars->fMiter? "miter":"two circuits");
    Abc_Print( -2, "\t-d     : toggle using dual output miter [default = %s]\n", pPars->fDualOutput? "yes":"no");
    Abc_Print( -2, "\t-t     : toggle using two-word miter [default = %s]\n", pPars->fTwoOutput? "yes":"no");
    Abc_Print( -2, "\t-b     : toggle working with Booth multipliers [default = %s]\n", pPars->fBooth? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManBoundaryMiter( Gia_Man_t * p1, Gia_Man_t * p2, int fVerbose );
    Gia_Man_t * pTemp, * pSecond;
    char * FileName = NULL;
    FILE * pFile = NULL;
    int c, fVerbose = 0;
    int bi  = 0;
    Extra_UtilGetoptReset();
    // TODO: use a flag to block Bnd_Man
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
            bi = atoi(argv[globalUtilOptind++]);
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
        Abc_Print( -1, "Abc_CommandAbc9BMiter(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9BMiter(): AIG should be given on the command line.\n" );
        return 0;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pSecond = Gia_AigerRead( FileName, 0, 0, 0 );
    if ( pSecond == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9BMiter(): Cannot read the file name on the command line.\n" );
        return 0;
    }    
    pTemp = Gia_ManBoundaryMiter( pAbc->pGia, pSecond, fVerbose );
    Gia_ManStop( pSecond );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &bmiter -I <biNum> [-vh] <file>\n" );
    Abc_Print( -2, "\t         creates the boundary miter\n" );
    Abc_Print( -2, "\t-I <biNum>:   number of boundary inputs\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the implementation file\n");    
    return 1;
}

/**Function*************************************************************

  Synopsis    [Handles boundary recovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BRecover( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec4_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars );
    extern void Cec4_ManSetParams( Cec_ParFra_t * pPars );
    extern Gia_Man_t * Gia_ManBoundaryMiter( Gia_Man_t * p1, Gia_Man_t * p2, int fVerbose );
    Gia_Man_t *pSpec, *pImpl_out = 0, *pSpec_out = 0, *pMiter, *pPatched = 0, *pTemp, *pBmiter;
    char * FileName = NULL;
    FILE * pFile = NULL;
    int c, fVerbose = 0, success = 1, fEq = 1, fEqOut = 1;

    // params
    Gps_Par_t Pars, * pPars = &Pars;
    memset( pPars, 0, sizeof(Gps_Par_t) );
    Cec_ParCec_t ParsCec, *pParsCec = &ParsCec;
    Cec_ManCecSetDefaultParams( pParsCec );
    Cec_ParFra_t ParsFra, *pParsFra = &ParsFra;
    Cec4_ManSetParams( pParsFra );
    pParsFra -> fBMiterInfo = 1;

    // parse options
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vhCkeo" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            pParsFra->fVerbose ^= 1;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParsFra->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParsFra->nBTLimit < 0 )
                goto usage;
            break;
        case 'k':
            pParsFra ->fUseCones ^= 1;
            break;
        case 'e':
            fEq ^= 1;
            break;
        case 'o':
            fEqOut ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9BRecover(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        printf("%d\n", argc-globalUtilOptind);
        Abc_Print( -1, "Abc_CommandAbc9BRecover(): AIG should be given on the command line.\n" );
        return 0;
    }

    // read spec
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );
    pSpec = Gia_AigerRead( FileName, 0, 1, 0 );
    if ( pSpec == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9BRecover(): Cannot read the file name on the command line.\n" );
        return 0;
    }    
    if ( Gia_ManBufNum(pSpec) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9BRecover(): The given spec should be hierarchical.\n" );
        Gia_ManStop(pSpec);
        return 0;
    }    

    // start boundary manager
    pBnd = Bnd_ManStart( pSpec, pAbc->pGia, fVerbose );

    // check boundary
    if ( 0 == Bnd_ManCheckBound( pSpec, fVerbose ) )
    {
        Abc_Print( -1, "Abc_CommandAbc9BRecover(): The given spec has invalid boundary.\n" );
        success = 0;
    }

    if ( success )
    {
        // create bmiter, run fraig, record mapping
        pBmiter = Bnd_ManStackGias( pSpec, pAbc->pGia );
        pTemp = Cec4_ManSimulateTest( pBmiter, pParsFra );

        // every output should be equivalent
        // else, terminate the command (TODO?)
        if ( !Bnd_ManCheckCoMerged( pTemp ) )
        {
            Abc_Print( -1, "Abc_CommandAbc9BRecover(): The given spec and impl cannot be proved equivalent.\n" );
            success = 0;
        }

        Gia_ManStop(pBmiter);
        Gia_ManStop(pTemp);
    }

    if ( success )
    {
        // find 
        Bnd_ManFindBound( pSpec, pAbc->pGia );

        // create spec_out and 
        pSpec_out = Bnd_ManGenSpecOut( pSpec );
        if ( !pSpec_out ) success = 0;
        pImpl_out = Bnd_ManGenImplOut( pAbc->pGia );
        if ( !pImpl_out ) success = 0;

        // Gia_AigerWrite( pSpec_out, "spec_out.aig", 0, 0, 0 );
        // Gia_AigerWrite( pImpl_out, "impl_out.aig", 0, 0, 0 );
        // Gia_ManPrintStats( pSpec_out, pPars );
        // Gia_ManPrintStats( pImpl_out, pPars );

        if ( !success )
        {
            printf("Abc_CommandAbc9BRecover(): The generated boundary is invalid. The circuit is not changed.\n");
        }
    }

    if ( success )
    {

        // check if spec_out and imnpl_out are equivalent
        if ( fVerbose ) 
        {
            if ( fEqOut )
            {
                printf("Checking the equivalence of spec_out and impl_out\n");
                pMiter = Gia_ManMiter( pSpec_out, pImpl_out, 0, 1, 0, 0, 0 );
                Bnd_ManSetEqOut( Cec_ManVerify( pMiter, pParsCec ) );
                Gia_ManStop( pMiter );
            }
            else
            {
                printf("Skip checking the equivalence of spec_out and impl_out\n");
            }
        }

        // generate patched impl
        if ( fVerbose ) printf("Generating patched impl\n");
        pPatched = Bnd_ManGenPatched1( pImpl_out, pSpec );

        // // generate patched spec just for debugging
        // printf("Generating patched spec\n");
        // pTemp = Bnd_ManGenPatched( pSpec_out, pAbc->pGia, pPatch );
        // printf("Checking the equivalence of patched spec and patched impl\n");
        // pMiter = Gia_ManMiter( pTemp, pPatched, 0, 1, 0, 0, 0 );
        // Cec_ManVerify( pMiter, pParsCec );
        // Gia_ManStop( pMiter );
        // printf("Checking the equivalence of patched spec and patch\n");
        // pMiter = Gia_ManMiter( pTemp, pPatch, 0, 1, 0, 0, 0 );
        // Cec_ManVerify( pMiter, pParsCec );
        // Gia_ManStop( pMiter );

        // Gia_ManStop( pTemp );

        // check if patched is equiv to spec
        if ( fVerbose ) 
        {
            if ( fEq ) printf("Checking the equivalence of patched impl and spec\n");
            else printf("Skip checking the equivalence of patched impl and spec\n");
        }
        if ( fEq )
        {
            pMiter = Gia_ManMiter( pSpec, pPatched, 0, 1, 0, 0, 0 );
            success = Cec_ManVerify( pMiter, pParsCec );
            Bnd_ManSetEqRes( success );
            if ( !success )
            {
                printf("Failed. The generated AIG is not equivalent.\n");
            }
            Gia_ManStop( pMiter );
        }

    }

    if ( fVerbose ) Bnd_ManPrintStats();

    Gia_ManStop( pSpec );
    if ( pSpec_out ) Gia_ManStop( pSpec_out );
    if ( pImpl_out ) Gia_ManStop( pImpl_out );
    if ( success )
    {
        if ( fEq ) printf("Success. The generated hierarchical impl is equivalent. (box size: %d -> %d)\n", Bnd_ManGetNInternal(), Bnd_ManGetNInternal() + Bnd_ManGetNExtra() );
        else printf("Success. But the equivalence in unknown (box size: %d -> %d)\n", Bnd_ManGetNInternal(), Bnd_ManGetNInternal() + Bnd_ManGetNExtra() );
    }
    if (pPatched) Abc_FrameUpdateGia( pAbc, pPatched );
    Bnd_ManStop();

    return 0;

usage:
    Abc_Print( -2, "usage: &brecover -I <biNum> [-vh] <impl> <patch>\n" );
    Abc_Print( -2, "\t         recover boundary using SAT-Sweeping\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-k     : toggle using logic cones in the SAT solver [default = %s]\n", pParsFra->fUseCones? "yes": "no" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pParsFra->nBTLimit );
    Abc_Print( -2, "\t-e     : toggle checking the equivalence of the result [default = %s]\n", fEq? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle checking the equivalence of the outsides in verbose [default = %s]\n", fEqOut? "yes": "no" );
    Abc_Print( -2, "\t<impl> : the implementation aig. (should be equivalent to spec)\n");    
    Abc_Print( -2, "\t<patch> : the modified spec. (should be a hierarchical AIG)\n");    
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9StrEco( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Cec4_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars );
    extern void Cec4_ManSetParams( Cec_ParFra_t * pPars );
    Gia_Man_t *pMiter, *pPatch, *pPatched;
    char * FileName = NULL;
    FILE * pFile = NULL;
    int c, success = 1;
    int fVerbose = 0, fSkipStrash = 0;

    // params
    Gps_Par_t Pars, * pPars = &Pars;
    memset( pPars, 0, sizeof(Gps_Par_t) );
    Cec_ParCec_t ParsCec, *pParsCec = &ParsCec;
    Cec_ManCecSetDefaultParams( pParsCec );
    Cec_ParFra_t ParsFra, *pParsFra = &ParsFra;
    Cec4_ManSetParams( pParsFra );
    pParsFra -> fBMiterInfo = 1;

    // parse options
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSkipStrash ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9StrEco(): There is no AIG.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        printf("%d\n", argc-globalUtilOptind);
        Abc_Print( -1, "Abc_CommandAbc9StrEco(): AIG should be given on the command line.\n" );
        return 0;
    }

    // read patch
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );
    pPatch = Gia_AigerRead( FileName, 0, 1, 0 );
    if ( pPatch == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9StrEco(): Cannot read the file name on the command line.\n" );
        return 0;
    }    

    // generate patched impl
    if ( fVerbose ) printf("Generating patched impl\n");
    pPatched = Bnd_ManGenPatched2( pAbc->pGia, pPatch, fSkipStrash, fVerbose );

    if ( pPatched )
    {
        // check if patched is equiv to patch
        if ( fVerbose ) printf("Checking the equivalence of patched impl and patch\n");
        pMiter = Gia_ManMiter( pPatch, pPatched, 0, 1, 0, 0, 0 );
        success = Cec_ManVerify( pMiter, pParsCec );
        if( !success ) 
        {
            printf("Failed. The patched circuit is not equivalent.\n");
        }
        Gia_ManStop( pMiter );
        Abc_FrameUpdateGia( pAbc, pPatched );
    }

    Gia_ManStop( pPatch );
    if ( success )
    {
        printf("Success. The patched circuit is equivalent.\n");
    }

    return 0;

usage:
    Abc_Print( -2, "usage: &str_eco -I <biNum> [-vh] <impl> <patch>\n" );
    Abc_Print( -2, "\t         SAT-sweeping-based ECO\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles skipping structural hash [default = %s]\n",  fSkipStrash? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<impl> : the implementation aig. (should be equivalent to spec)\n");    
    Abc_Print( -2, "\t<patch> : the modified spec. (should be a hierarchical AIG)\n");    
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
