/**CFile****************************************************************

  FileName    [abcArith.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Arithmetic processing.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "proof/acec/acec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandATMap                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Fadds              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ATree              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Polyn              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Anorm              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Decla              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ProdAdd            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenComp            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenSorter          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenNeuron          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenAdder           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GenPrefix          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MulFind            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MulFind3           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BsFind             ( Abc_Frame_t * pAbc, int argc, char ** argv );

#ifdef __cplusplus
extern "C" {
#endif

int* adder_return_array(int width, int mfo, int use_or, int seed, int num_rounds, int delay_relaxation, int fVerbose, int fDumpVer, int fDumpMiter,  int* pnObjs, int* pnIns, int* pnLatches, int* pnOuts, int* pnAnds);

#ifdef __cplusplus
}
#endif

/**Function*************************************************************

  Synopsis    [Registers arithmetic processing commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitArith( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Sequential",   "atmap",         Abc_CommandATMap,            0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&fadds",        Abc_CommandAbc9Fadds,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&atree",        Abc_CommandAbc9ATree,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&polyn",        Abc_CommandAbc9Polyn,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&anorm",        Abc_CommandAbc9Anorm,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&decla",        Abc_CommandAbc9Decla,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&prodadd",      Abc_CommandAbc9ProdAdd,                0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gencomp",      Abc_CommandAbc9GenComp,                0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gensorter",    Abc_CommandAbc9GenSorter,              0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&genneuron",    Abc_CommandAbc9GenNeuron,              0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&genadder",     Abc_CommandAbc9GenAdder,               0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&genprefix",    Abc_CommandAbc9GenPrefix,              0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mulfind",      Abc_CommandAbc9MulFind,                0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mulfind3",     Abc_CommandAbc9MulFind3,               0 );    
    Cmd_CommandAdd( pAbc, "ABC9",         "&bsfind",       Abc_CommandAbc9BsFind,                 0 );    
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
int Abc_CommandATMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkATMap( int nXVars, int nYVars, int nAdder, char ** pGPC, int nGPCs, int fReturn, int fVerbose );
    int c, nXVars = -1, nYVars = -1, nAdder = 2, fReturn = 0, fVerbose = 1;
    char * pGPCs0[1] = { (char*)"3:11:1" };
    char ** pGPCs = NULL; int nGPCs = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "XYArvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'X':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-X\" should be followed by a file name.\n" );
                goto usage;
            }
            nXVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by a file name.\n" );
                goto usage;
            }
            nYVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            nAdder = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'r':
            fReturn ^= 1;
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
    if ( nAdder < 2 || nAdder > 4 )
    {
        printf( "The terminal adder should have 2, 3, or 4 bits.\n" );
        return 0;
    }
    pGPCs = argv + globalUtilOptind;
    nGPCs = argc - globalUtilOptind;
    if ( nGPCs == 0 )
    {
        printf( "GPCs are not listed on the command line. The simplest GPC (full adder) will be used.\n" );
        pGPCs = pGPCs0;
        nGPCs = 1;
    }
    Abc_NtkATMap( nXVars, nYVars, nAdder, pGPCs, nGPCs, fReturn, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: atmap [-XYA num] [-G str] [-rv] <GPC(0)> <GPC(1)> ... <GPC(N-1)>\n" );
    Abc_Print( -2, "\t           maps rectangular adder tree using GPCs\n" );
    Abc_Print( -2, "\t-X <num> : the number of different ranks [default = %d]\n", nXVars );
    Abc_Print( -2, "\t-Y <num> : the number of bits of each rank [default = %d]\n", nYVars );
    Abc_Print( -2, "\t-A <num> : the number of arguments in the terminal adder [default = %d]\n", nAdder );
    Abc_Print( -2, "\t-r       : return to the first GPC after each step [default = %s]\n", fReturn? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n\n");
    Abc_Print( -2, "\t           For example, to map an adder tree with dimensions 4 x 648 using GPC(6,6,6,6:1,2,2,2,2,1)\n" );
    Abc_Print( -2, "\t           having LUT efficiency E = 1.75, use the command line \"atmap -X 4 -Y 648 6666:122221:8 3:11:1\"\n" );
    Abc_Print( -2, "\t           where 8 is the number of 6-LUTs needed to implement the GPC and E = (24-10)/8 = 1.75.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Fadds( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupWithNaturalBoxes( Gia_Man_t * p, int nFaddMin, int fVerbose );
    extern Gia_Man_t * Gia_ManDupWithArtificialBoxes( Gia_Man_t * p, int DelayC, int nPathMin, int nPathMax, int nPathLimit, int fUseFanout, int fXorTrick, int fIgnoreBoxDelays, int fVerbose );
    Gia_Man_t * pTemp, * pTemp2;
    int c, nFaddMin = 3, fUseNat = 0, fUseArt = 0, fVerbose = 0;
    int DelayC = 0, nPathMin = 3, nPathMax = 32, nPathLimit = 50, fUseFanout = 0, fUseXorTrick = 0, fIgnoreBoxDelays = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NBSLPnafxbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaddMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFaddMin < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            DelayC = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayC < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nPathMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPathMin < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nPathMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPathMax < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPathLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPathLimit < 0 )
                goto usage;
            break;
        case 'n':
            fUseNat ^= 1;
            break;
        case 'a':
            fUseArt ^= 1;
            break;
        case 'f':
            fUseFanout ^= 1;
            break;
        case 'x':
            fUseXorTrick ^= 1;
            break;
        case 'b':
            fIgnoreBoxDelays ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Fadds(): There is no AIG.\n" );
        return 0;
    }
    if ( fUseNat )
        pTemp = Gia_ManDupWithNaturalBoxes( pAbc->pGia, nFaddMin, fVerbose );
    else
    {
        pTemp = Gia_ManDup( pAbc->pGia );
        Gia_ManTransferTiming( pTemp, pAbc->pGia );
    }
    if ( fUseArt )
        pTemp2 = Gia_ManDupWithArtificialBoxes( pTemp, DelayC, nPathMin, nPathMax, nPathLimit, fUseFanout, fUseXorTrick, fIgnoreBoxDelays, fVerbose );
    else
    {
        pTemp2 = Gia_ManDup( pTemp );
        Gia_ManTransferTiming( pTemp2, pTemp );
    }
    Gia_ManStop( pTemp );
    Abc_FrameUpdateGia( pAbc, pTemp2 );
    return 0;
usage:
    Abc_Print( -2, "usage: &fadds [-NBSLP num] [-nafxvh]\n" );
    Abc_Print( -2, "\t         detects full-adder chains and puts them into white boxes\n" );
    Abc_Print( -2, "\t-n     : toggles detecting natural full-adder chains [default = %s]\n",              fUseNat? "yes": "no" );
    Abc_Print( -2, "\t-N num : minimum length of a natural full-adder chain to detect [default = %d]\n",   nFaddMin );
    Abc_Print( -2, "\t-a     : toggles detecting artificial full-adder chains [default = %s]\n",           fUseArt? "yes": "no" );
    Abc_Print( -2, "\t-B num : full-adder box delay (percentage of AND-gate delay) [default = %d]\n",      DelayC );
    Abc_Print( -2, "\t-S num : minimum length of an artificial full-adder chain [default = %d]\n",         nPathMin );
    Abc_Print( -2, "\t-L num : maximum length of an artificial full-adder chain [default = %d]\n",         nPathMax );
    Abc_Print( -2, "\t-P num : maximum number of artificial full-adder chains to detect [default = %d]\n", nPathLimit );
    Abc_Print( -2, "\t-f     : toggles allowing external fanouts in artificial chains [default = %s]\n",   fUseFanout? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggles using XOR to generate fanouts in artificial chains [default = %s]\n",   fUseXorTrick? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles ignoring boxes when computing delays [default = %s]\n",             fIgnoreBoxDelays? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",                     fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ATree( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_PolynCoreDetectTest( Gia_Man_t * pGia, int fAddExtra, int fAddCones, int fVerbose );
    Gia_Man_t * pTemp = NULL;
    int c, fAddExtra = 0, fAddCones = 0, fVerbose = 0, fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ecvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'e':
            fAddExtra ^= 1;
            break;
        case 'c':
            fAddCones ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Esop(): There is no AIG.\n" );
        return 0;
    }
    pTemp = Gia_PolynCoreDetectTest( pAbc->pGia, fAddExtra, fAddCones, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &atree [-ecvwh]\n" );
    Abc_Print( -2, "\t         extracts adder tree rooting in primary outputs\n" );
    Abc_Print( -2, "\t-e     : toggles adding extra outputs [default = %s]\n",  fAddExtra? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggles duplicating complete AIG [default = %s]\n",  fAddCones? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles printing very verbose information [default = %s]\n",  fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Polyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_PolynBuild2Test( Gia_Man_t * pGia, char * pSign, int nExtra, int fSigned, int fVerbose, int fVeryVerbose );
    Vec_Int_t * vOrder = NULL; char * pSign = NULL;
    int c, nExtra = 0, fOld = 0, fSimple = 1, fSigned = 0, fVerbose = 0, fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSoasvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nExtra = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nExtra < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a char string without spaces.\n" );
                goto usage;
            }
            pSign = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'o':
            fOld ^= 1;
            break;
        case 'a':
            fSimple ^= 1;
            break;
        case 's':
            fSigned ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Esop(): There is no AIG.\n" );
        return 0;
    }
    if ( argc >= globalUtilOptind + 1 )
    {
        printf( "Trailing symbols on the command line (\"%s\").\n", argv[globalUtilOptind] );
        return 0;
    }
    if ( fOld )
    {
        vOrder = fSimple ? NULL : Gia_PolynReorder( pAbc->pGia, fVerbose, fVeryVerbose );
        Gia_PolynBuild( pAbc->pGia, vOrder, fSigned, fVerbose, fVeryVerbose );
        Vec_IntFreeP( &vOrder );
    }
    else
        Gia_PolynBuild2Test( pAbc->pGia, pSign, nExtra, fSigned, fVerbose, fVeryVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &polyn [-N num] [-oasvwh] [-S str]\n" );
    Abc_Print( -2, "\t         derives algebraic polynomial from AIG\n" );
    Abc_Print( -2, "\t-N num : the number of additional primary outputs (-1 = unused) [default = %d]\n", nExtra );
    Abc_Print( -2, "\t-o     : toggles old computation [default = %s]\n",  fOld? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggles simple computation [default = %s]\n",  fSimple? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles signed computation [default = %s]\n",  fSigned? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n",  fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles printing very verbose information [default = %s]\n",  fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t\n");
    Abc_Print( -2, "\t-S str : (optional) the output signature as a character string\n" );
    Abc_Print( -2, "\t         The format used to represent the output signature is very restrictive.\n" );
    Abc_Print( -2, "\t         It should be a string without spaces containing monomials in terms of\n" );
    Abc_Print( -2, "\t         inputs (i<num>) and outputs (o<num>) where <num> is 0-based. Coefficients\n" );
    Abc_Print( -2, "\t         are degrees of two, represented by log2 of their value: for example, \n" );
    Abc_Print( -2, "\t         \"2\" is 2^2 = 4, \"-4\" is -2^4=-16, \"-0\" is -2^0=-1, etc\n" );
    Abc_Print( -2, "\t         Two types of signature are accepted:\n" );
    Abc_Print( -2, "\t         (1) a sequence of monomials without parentheses (for example, \"-2*o0+1*o1+0*o2\")\n" );
    Abc_Print( -2, "\t         (2) a product of two sequences followed by a sum with a sequence\n" );
    Abc_Print( -2, "\t             (for example, \"(4*o0+2*o1+1*o2)*(4*i3+2*i4+1*i5)+(4*o3+2*o4+1*o5)\")\n" );
    Abc_Print( -2, "\t         Here is the signature of a signed 2-bit multiplier: \"(0*o0+1*o1+2*o2-3*o3)\"\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Anorm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fBooth = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBooth ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Anorm(): There is no AIG.\n" );
        return 0;
    }
    pTemp = Acec_Normalize( pAbc->pGia, fBooth, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &anorm [-bvh]\n" );
    Abc_Print( -2, "\t         normalize adder trees in the current AIG\n" );
    Abc_Print( -2, "\t-b     : toggles working with Booth multipliers [default = %s]\n",  fBooth? "yes": "no" );
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
int Abc_CommandAbc9Decla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fBooth = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBooth ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Decla(): There is no AIG.\n" );
        return 0;
    }
    pTemp = Acec_ManDecla( pAbc->pGia, fBooth, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &decla [-bvh]\n" );
    Abc_Print( -2, "\t         removes carry look ahead adders\n" );
    Abc_Print( -2, "\t-b     : toggles working with Booth multipliers [default = %s]\n",  fBooth? "yes": "no" );
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
int Abc_CommandAbc9ProdAdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int nArgA       =   4;
    int nArgB       =   4;
    int Seed        =   0;
    int fSigned     =   0;
    int fCla        =   0;
    int c, fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ABSscvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nArgA = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nArgA < 0 )
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nArgB = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nArgB < 0 )
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
        case 's':
            fSigned ^= 1;
            break;
        case 'c':
            fCla ^= 1;
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
    Gia_ManProdAdderGen( nArgA, nArgB, Seed, fSigned, fCla );
    return 0;

usage:
    Abc_Print( -2, "usage: &prodadd [-ABSscvh]\n" );
    Abc_Print( -2, "\t          generates partial products and adder trees\n" );
    Abc_Print( -2, "\t-A num  : the bit-width of the first arg [default = %d]\n",           nArgA );
    Abc_Print( -2, "\t-B num  : the bit-width of the second arg [default = %d]\n",          nArgB );
    Abc_Print( -2, "\t-S num  : random seed used the node ordering [default = %d]\n",       Seed );
    Abc_Print( -2, "\t-s      : toggle using signed operation [default = %s]\n",            fSigned? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggle using CLA in the adder tree [default = %s]\n",       fCla? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information [default = %s]\n",      fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenComp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupGenComp( int nBits, int fInterleave, int fSigned );
    Gia_Man_t * pTemp = NULL;
    int c, nBits = 4, fInter = 0, fSigned = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kisvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nBits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBits < 0 )
                goto usage;
            break;
        case 'i':
            fInter ^= 1;
            break;            
        case 's':
            fSigned ^= 1;
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
    if ( nBits == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenComp(): The number of inputs should be defined on the command line \"-K num\".\n" );
        return 0;            
    }    
    pTemp = Gia_ManDupGenComp( nBits, fInter, fSigned );
    Abc_FrameUpdateGia( pAbc, pTemp );
    if ( fVerbose )
        Abc_Print( 1, "Generated %d-bit comparator.\n", nBits );
    return 0;

usage:
    Abc_Print( -2, "usage: &gencomp [-K <num>] [-isvh]\n" );
    Abc_Print( -2, "\t         generates the comparator (a > b)\n" );
    Abc_Print( -2, "\t-K num : the bitwidth of the inputs [default = %d]\n", nBits );
    Abc_Print( -2, "\t-i     : toggles using interleaved variable ordering [default = %s]\n", fInter ? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles generating signed comparator [default = %s]\n", fSigned ? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenSorter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenSorter( int LogN );
    Gia_Man_t * pTemp = NULL;
    int c, LogN = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            LogN = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( LogN < 0 )
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
    if ( LogN == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenComp(): The number of inputs should be defined on the command line \"-K num\".\n" );
        return 0;            
    }    
    pTemp = Gia_ManGenSorter( LogN );
    Abc_FrameUpdateGia( pAbc, pTemp );
    if ( fVerbose )
        Abc_Print( 1, "Generated %d-input sorter composed of %d elementary 2-bit sorters.\n", 1 << LogN, (1 << LogN) * LogN * (LogN-1) / 4 + (1 << LogN) - 1 );
    return 0;

usage:
    Abc_Print( -2, "usage: &gensorter [-K <num>] [-vh]\n" );
    Abc_Print( -2, "\t         generates the sorter using pair-wise sorting algorithm\n" );
    Abc_Print( -2, "\t-K num : the base-2 log of the number of inputs [default = undefined]\n" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenNeuron( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenNeuron( char * pFileName, int nIBits, int nLutSize, int fDump, int fVerbose );
    Gia_Man_t * pTemp = NULL;
    int c, nBits = 0, nLutSize = 0, fDump = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IKdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nBits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBits < 0 )
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
    if ( nBits < 1 || nBits > 31 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenNeuron(): The number of inputs (0 < K < 32) should be defined on the command line \"-K num\".\n" );
        return 0;            
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( 1, "Input file is not given.\n" );
        return 0;
    }
    pTemp = Gia_ManGenNeuron( argv[globalUtilOptind], nBits, nLutSize, fDump, fVerbose );
    if ( fVerbose )
        printf( "Generated %d-argument neuron with %d-bit inputs and %d-bit output.\n", Gia_ManCiNum(pTemp)/nBits, nBits, Gia_ManCoNum(pTemp) );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &genneuron [-IK <num>] [-dvh] <file>\n" );
    Abc_Print( -2, "\t         generates the implementation of one neuron\n" );
    Abc_Print( -2, "\t-I num : the bit-width of each input [default = undefined]\n" );
    Abc_Print( -2, "\t-K num : the LUT size for logic structuring [default = undefined]\n" );
    Abc_Print( -2, "\t-d     : toggles dumping RTL Verilog [default = %s]\n", fDump ? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the weights one per line followed by the bias (in hex notation)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenAdder( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManGenAdder( int nVars, int fSK, int fBK, int fHC, int fMM, int fCarries, int fVerbose );
    Gia_Man_t * pTemp = NULL;
    int c, nBits = 0, fSK = 0, fBK = 0, fHC = 0, fMM = 0, fCarries = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nsbhmcv" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nBits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBits < 0 )
                goto usage;
            break;
        case 's':
            fSK ^= 1;
            break;
        case 'b':
            fBK ^= 1;
            break;
        case 'h':
            fHC ^= 1;
            break;
        case 'm':
            fMM ^= 1;
            break;
        case 'c':
            fCarries ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( nBits < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenAdder(): The number of inputs should be defined on the command line \"-N num\".\n" );
        return 0;            
    }
    pTemp = Gia_ManGenAdder( nBits, fSK, fBK, fHC, fMM, fCarries, fVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &genadder [-N <num>] [-sbhmcv]\n" );
    Abc_Print( -2, "\t         generates a prefix adder (by default, the ripple carry adder)\n" );
    Abc_Print( -2, "\t-N num : the bit-width of the adder [default = undefined]\n" );
    Abc_Print( -2, "\t-s     : toggles using Sklansky adder [default = %s]\n", fSK ? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles using Brent-Kung adder [default = %s]\n", fBK ? "yes": "no" );
    Abc_Print( -2, "\t-h     : toggles using Huan-Carlsson adder [default = %s]\n", fHC ? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles using majority-based M/M adder [default = %s]\n", fMM ? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggles using carry-in and carry-out [default = %s]\n", fCarries ? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GenPrefix( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManDupFromArray( int * pObjs, int nObjs, int nIns, int nLatches, int nOuts, int nAnds );
    int c, nBits = 8, nFans = 4, Seed = 0, nIters = 1, DelayRelax = 0, fDumpVer = 0, fDumpMiter = 0, fVerbose = 0, use_or = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NFSIRdmov" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nBits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBits < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFans = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFans < 0 )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            DelayRelax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayRelax < 0 )
                goto usage;
            break;


        case 'd':
            fDumpVer ^= 1;
            break;
        case 'm':
            fDumpMiter ^= 1;
            break;
        case 'o':
            use_or ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( nBits < 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9GenPrefix(): The number of inputs should be defined on the command line \"-N num\".\n" );
        return 0;            
    }
    else
    {
         int nObjs = 0, nIns = 0, nLatches = 0, nOuts = 0, nAnds = 0;
         int * pObjs = adder_return_array( nBits, nFans, use_or, Seed, nIters, DelayRelax, fVerbose, fDumpVer, fDumpMiter,   &nObjs, &nIns, &nLatches, &nOuts, &nAnds );
         if ( pObjs == NULL ) {
            printf( "Prefix tree with %d inputs and %d maximum fanout does not exist.\n", nBits, nFans );
         } else {
            Gia_Man_t * pTemp = Gia_ManDupFromArray( pObjs, nObjs, nIns, nLatches, nOuts, nAnds );
            Abc_FrameUpdateGia( pAbc, pTemp );
            ABC_FREE( pObjs );
         }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &genprefix [-NFSIR <num>] [-dmov]\n" );
    Abc_Print( -2, "\t         generates a prefix adder with minimum depth\n" );
    Abc_Print( -2, "\t-N num : the bit-width of the adder [default = %d]\n", nBits );
    Abc_Print( -2, "\t-F num : the limit on the fanout count [default = %d]\n", nFans );
    Abc_Print( -2, "\t-S num : the random seed used to randomize search [default = %d]\n", Seed );
    Abc_Print( -2, "\t-I num : the number of iterations to find the smallest prefix tree [default = %d]\n", nIters );
    Abc_Print( -2, "\t-R num : the delay relaxation (the max allowed level increase over log2(N)) [default = %d]\n", DelayRelax );
    Abc_Print( -2, "\t-d     : toggles dumping the adder in Verilog [default = %s]\n", fDumpVer ? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles dumping the miter in Verilog [default = %s]\n", fDumpMiter ? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggles using additional optimization [default = %s]\n", use_or ? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles printing verbose information [default = %s]\n\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t         The code of this command is contributed by Martin Povišer <povik@cutebit.org>\n\n" );
    Abc_Print( -2, "\t         The implementation is inspired by S. Roy, M. Choudhury, R. Puri, D. Pan,\n" );
    Abc_Print( -2, "\t         \"Polynomial time algorithm for area and power efficient adder synthesis\n" );
    Abc_Print( -2, "\t         in high-performance designs\", Proc. ASP-DAC 2015.\n" );
    Abc_Print( -2, "\t         https://www.cerc.utexas.edu/utda/publications/C166.pdf\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MulFind( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManMulFind( Gia_Man_t * p, int nCutNum, int fVerbose );
    int c, nCutNum = 8, fVerbose = 0;
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
            nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutNum < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9MulFind(): There is no AIG.\n" );
        return 0;
    }
    Gia_ManMulFind( pAbc->pGia, nCutNum, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &mulfind [-C num] [-vh]\n" );
    Abc_Print( -2, "\t          detects multipliers in the given AIG\n" );
    Abc_Print( -2, "\t-C num  : the number of cuts to compute at each node [default = %d]\n", nCutNum );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MulFind3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManMulFindNew( Gia_Man_t * p, int nABits, int nFanLim, int fLits, int fVerbose );
    int c, nABits = 0, nFanLim = 4, fLits = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IFlvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nABits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nABits < 0 )
                goto usage;
            break;            
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFanLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFanLim < 0 )
                goto usage;
            break;            
        case 'l':
            fLits ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9MulFind(): There is no AIG.\n" );
        return 0;
    }
    Gia_ManMulFindNew( pAbc->pGia, nABits, nFanLim, fLits, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &mulfind3 [-IF num] [-lvh]\n" );
    Abc_Print( -2, "\t          detects multipliers in the given AIG\n" );
    Abc_Print( -2, "\t-I num  : the bit-width of the first input if known [default = %d]\n", nABits );
    Abc_Print( -2, "\t-F num  : the fanout limit [default = %d]\n", nFanLim );
    Abc_Print( -2, "\t-l      : toggles using literals instead of nodes [default = %s]\n", fLits ? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BsFind( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManBsFindBest( Gia_Man_t * pGia, int nWords, int nLutSize, int nBest, int nIterMax, int fVerbose );
    int c, nWords = 256, nLutSize = 6, nBest = 20, nIterMax = 10, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WKBIvh" ) ) != EOF )
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
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBest = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBest < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9MulFind(): There is no AIG.\n" );
        return 0;
    }
    Gia_ManBsFindBest( pAbc->pGia, nWords, nLutSize, nBest, nIterMax, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &bsfind [-WKBI num] [-vh]\n" );
    Abc_Print( -2, "\t         found a good boundset for the multi-output function\n" );
    Abc_Print( -2, "\t-W num  : the number of simulation words to use [default = %d]\n", nWords );
    Abc_Print( -2, "\t-K num  : the number of bound-set variables (LUT size) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-B num  : the number of best bound-sets to consider [default = %d]\n", nBest );
    Abc_Print( -2, "\t-I num  : the number of refinement iterations to perform [default = %d]\n", nIterMax );
    Abc_Print( -2, "\t-v      : toggles printing verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
