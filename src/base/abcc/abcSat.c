/**CFile****************************************************************

  FileName    [abcSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [SAT and QBF solving.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "sat/xsat/xsat.h"
#include "sat/satoko/satoko.h"
#include "sat/cnf/cnf.h"
#include "proof/cec/cec.h"
#include "opt/cut/cut.h"

#ifndef _WIN32
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandRunSat                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMinisat                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMinisimp               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandISat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQbf                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSat                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDSat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandXSat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSatoko                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Satoko             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sat3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Kissat             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPSat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sat                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatEnum            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SplitSat           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SatTest            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Qbf                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9HomoQbf            ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers sat and qbf solving commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitSat( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "runsat",        Abc_CommandRunSat,           0 );    
    Cmd_CommandAdd( pAbc, "Various",      "minisat",       Abc_CommandMinisat,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "minisimp",      Abc_CommandMinisimp,         0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "isat",          Abc_CommandISat,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "qbf",           Abc_CommandQbf,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "sat",           Abc_CommandSat,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "dsat",          Abc_CommandDSat,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "xsat",          Abc_CommandXSat,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "satoko",        Abc_CommandSatoko,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "&satoko",       Abc_CommandAbc9Satoko,       0 );
    Cmd_CommandAdd( pAbc, "Verification", "&sat3",         Abc_CommandAbc9Sat3,         0 );
    Cmd_CommandAdd( pAbc, "Verification", "&kissat",       Abc_CommandAbc9Kissat,       0 );
    Cmd_CommandAdd( pAbc, "Verification", "psat",          Abc_CommandPSat,             0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sat",          Abc_CommandAbc9Sat,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&satenum",      Abc_CommandAbc9SatEnum,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&splitsat",     Abc_CommandAbc9SplitSat,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sattest",      Abc_CommandAbc9SatTest,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&qbf",          Abc_CommandAbc9Qbf,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&homoqbf",      Abc_CommandAbc9HomoQbf,      0 );
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
int Abc_CommandRunSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile = NULL;
    char * pFileCnf = NULL;
    int c, i, fWalk = 0, fKissat = 0, nIters = 10, fVerbose = 0;
    abctime clk;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ikwvh" ) ) != EOF )
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
        case 'k':
            fKissat ^= 1;
            break;           
        case 'w':
            fWalk ^= 1;
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
    if ( fKissat + fWalk != 1 ) {
        printf( "Exactly one SAT solver should be selected.\n" );
        return 1;   
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    pFileCnf = argv[globalUtilOptind];
    pFile = fopen( pFileCnf, "rb" );
    if ( pFile == NULL ) {
        printf( "The file \"%s\" cannot be found.\n", pFileCnf );
        return 1;
    }
    fclose( pFile );
    clk = Abc_Clock();
    for ( i = 0; i < nIters; i++ ) {
        char pCommand[1000];
        if ( fKissat )
            sprintf( pCommand, "kissat -q --seed=%d %s", i, pFileCnf );
        else if ( fWalk )
            sprintf( pCommand, "walk -s%d %s", i, pFileCnf );
#if defined(__wasm)
        if (1) {
#else
        if (system(pCommand) == -1) {
#endif
            fprintf(stdout, "Command \"%s\" did not succeed.\n", pCommand);
            return 0;
        }
    }
    printf( "Performed %d iterations of SAT solving. ", nIters );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return 0;

usage:
    Abc_Print( -2, "usage: runsat [-I num] [-kwvh] <cnf_file>\n" );
    Abc_Print( -2, "\t         performs randomized iterations of SAT solving\n" );
    Abc_Print( -2, "\t-I num : the number of iterations [default = %d]\n", nIters );
    Abc_Print( -2, "\t-k     : toggle using Kissat (binary name \"kissat\") [default = %s]\n", fKissat? "yes": "no" );    
    Abc_Print( -2, "\t-w     : toggle using WalkSat (binary name \"walk\") [default = %s]\n", fWalk? "yes": "no" );    
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
int Abc_CommandISat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    int nConfLimit;

    extern Abc_Ntk_t * Abc_NtkIvySat( Abc_Ntk_t * pNtk, int nConfLimit, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
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
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvySat( pNtk, nConfLimit, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: isat [-C num] [-vh]\n" );
    Abc_Print( -2, "\t         tries to prove the miter constant 0\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
//    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
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
int Abc_CommandQbf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nPars;
    int nIters;
    int fDumpCnf;
    int fVerbose;

    extern void Abc_NtkQbf( Abc_Ntk_t * pNtk, int nPars, int nIters, int fDumpCnf, int fVerbose );
    // set defaults
    nPars    =  -1;
    nIters   = 500;
    fDumpCnf =   0;
    fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PIdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPars < 0 )
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
        case 'd':
            fDumpCnf ^= 1;
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
        Abc_Print( -1, "Works only for combinational networks.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "The miter should have one primary output.\n" );
        return 1;
    }
    if ( !(nPars > 0 && nPars < Abc_NtkPiNum(pNtk)) )
    {
        Abc_Print( -1, "The number of parameter variables is invalid (should be > 0 and < PI num).\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkQbf( pNtk, nPars, nIters, fDumpCnf, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 1, 0 );
        Abc_NtkQbf( pNtk, nPars, nIters, fDumpCnf, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: qbf [-PI num] [-dvh]\n" );
    Abc_Print( -2, "\t         solves QBF problem EpVxM(p,x)\n" );
    Abc_Print( -2, "\t-P num : number of parameters p (should be the first PIs) [default = %d]\n", nPars );
    Abc_Print( -2, "\t-I num : quit after the given iteration even if unsolved [default = %d]\n", nIters );
    Abc_Print( -2, "\t-d     : toggle dumping QDIMACS file instead of solving [default = %s]\n", fDumpCnf? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t         Consider specification of the two-input XOR and its implementation in the form of a 4:1 MUX:\n\n" );
    Abc_Print( -2, "\t         > # file s.blif\n" );
    Abc_Print( -2, "\t         > .model xor2\n" );
    Abc_Print( -2, "\t         > .inputs d0 d1 d2 d3 a b\n" );
    Abc_Print( -2, "\t         > .outputs F\n" );
    Abc_Print( -2, "\t         > .names a b F\n" );
    Abc_Print( -2, "\t         > 01 1\n" );
    Abc_Print( -2, "\t         > 10 1\n" );
    Abc_Print( -2, "\t         > .end\n\n" );
    Abc_Print( -2, "\t         > # file i.blif\n" );
    Abc_Print( -2, "\t         > .model mux41\n" );
    Abc_Print( -2, "\t         > .inputs d0 d1 d2 d3 a b\n" );
    Abc_Print( -2, "\t         > .outputs F\n" );
    Abc_Print( -2, "\t         > .names d0 d1 d2 d3 a b F\n" );
    Abc_Print( -2, "\t         > 1---00 1\n" );
    Abc_Print( -2, "\t         > -1--10 1\n" );
    Abc_Print( -2, "\t         > --1-01 1\n" );
    Abc_Print( -2, "\t         > ---111 1\n" );
    Abc_Print( -2, "\t         > .end\n\n" );
    Abc_Print( -2, "\t         The following run shows how to assign data inputs to the MUX (the first 4 inputs of the miter) to get the XOR:\n\n" );
    Abc_Print( -2, "\t         > abc 51> miter -n i.blif s.blif; st -i; ps\n" );
    Abc_Print( -2, "\t         > i_s_miter: i/o =    6/    1  lat =    0  and =     15  lev =  6\n\n" );
    Abc_Print( -2, "\t         > abc 53> qbf -P 4\n" );
    Abc_Print( -2, "\t         > Parameters: 0110  Statistics: 0=2 1=2\n" );
    Abc_Print( -2, "\t         > Solved after 1 iterations.  Total runtime =     0.00 sec\n\n" );
    Abc_Print( -2, "\t         > abc 53> &get; &qbf -P 4\n" );
    Abc_Print( -2, "\t         > Parameters: 0110  Statistics: 0=2 1=2\n" );
    Abc_Print( -2, "\t         > The problem is SAT after 2 iterations.  Time =     0.00 sec\n\n" );
    Abc_Print( -2, "\t         What we synthesized is the truth table of the XOR gate!\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMinisat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
#ifdef USE_MINISAT22
    extern int MainSat(int argc, char** argv);
    MainSat( argc, argv );
#else
    printf( "This command is currently disabled.\n" );
#endif
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs the simplifying MiniSAT interface.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMinisimp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
#ifdef USE_MINISAT22
    extern int MainSimp(int argc, char** argv);
    MainSimp( argc, argv );
#else
    printf( "This command is currently disabled.\n" );
#endif
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int RetValue;
    int fVerbose;
    int nConfLimit;
    int nInsLimit;
    abctime clk;
    // set defaults
    fVerbose   = 0;
    nConfLimit = 0;
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CIvh" ) ) != EOF )
    {
        switch ( c )
        {
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
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    }

    clk = Abc_Clock();
    if ( Abc_NtkIsStrash(pNtk) )
    {
        RetValue = Abc_NtkMiterSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, fVerbose, NULL, NULL );
    }
    else
    {
        assert( Abc_NtkIsLogic(pNtk) );
        Abc_NtkToBdd( pNtk );
        RetValue = Abc_NtkMiterSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, fVerbose, NULL, NULL );
    }

    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        //int i;
        //Abc_Obj_t * pObj;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        // print model
//        Abc_NtkForEachPi( pNtk, pObj, i )
//        {
//            Abc_Print( -1, "%d", (int)(pNtk->pModel[i] > 0) );
//            if ( i == 70 )
//                break;
//        }
//        Abc_Print( -1, "\n" );
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
    return 0;

usage:
    Abc_Print( -2, "usage: sat [-C num] [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    Abc_Print( -2, "\t         derives CNF from the current network and leave it unchanged\n" );
    Abc_Print( -2, "\t         (there is also a newer SAT solving command \"dsat\")\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
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
int Abc_CommandDSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int RetValue;
    int fAlignPol;
    int fAndOuts;
    int fNewSolver;
    int fSilent;
    int fShowPattern;
    int fVerbose;
    int nConfLimit;
    int nLearnedStart;
    int nLearnedDelta;
    int nLearnedPerce;
    int nInsLimit;
    abctime clk;

    extern int Abc_NtkDSat( Abc_Ntk_t * pNtk, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int nLearnedStart, int nLearnedDelta, int nLearnedPerce, int fAlignPol, int fAndOuts, int fNewSolver, int fVerbose );
    // set defaults
    fAlignPol  = 0;
    fAndOuts   = 0;
    fNewSolver = 0;
    fSilent    = 0;
    fShowPattern = 0;
    fVerbose   = 0;
    nConfLimit = 0;
    nInsLimit  = 0;
    nLearnedStart = 0;
    nLearnedDelta = 0;
    nLearnedPerce = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CILDEpansvwh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedStart < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedDelta < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedPerce = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedPerce < 0 )
                goto usage;
            break;
        case 'p':
            fAlignPol ^= 1;
            break;
        case 'a':
            fAndOuts ^= 1;
            break;
        case 'n':
            fNewSolver ^= 1;
            break;
        case 's':
            fSilent ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fShowPattern ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc == globalUtilOptind + 1 )
    {
        int * pModel = NULL;
        extern int Cnf_DataSolveFromFile( char * pFileName, int nConfLimit, int nLearnedStart, int nLearnedDelta, int nLearnedPerce, int fVerbose, int fShowPattern, int ** ppModel, int nPis );
        // get the input file name
        char * pFileName = argv[globalUtilOptind];
        FILE * pFile = fopen( pFileName, "rb" );
        if ( pFile == NULL )
        {
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
            return 0;
        }
        fclose( pFile );
        Cnf_DataSolveFromFile( pFileName, nConfLimit, nLearnedStart, nLearnedDelta, nLearnedPerce, fVerbose, fShowPattern, &pModel, pNtk ? Abc_NtkPiNum(pNtk) : 0 );
        if ( pModel && pNtk )
        {
            int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pModel );
            if ( pSimInfo[0] != 1 )
                Abc_Print( 1, "ERROR in mapping PIs into SAT vars: Generated CEX is invalid.\n" );
            ABC_FREE( pSimInfo );
            pAbc->pCex = Abc_CexCreate( 0, Abc_NtkPiNum(pNtk), pModel, 0, 0, 0 );
        }
        ABC_FREE( pModel );
        return 0;
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

    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently expects a single-output miter.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    clk = Abc_Clock();
    RetValue = Abc_NtkDSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, nLearnedStart, nLearnedDelta, nLearnedPerce, fAlignPol, fAndOuts, fNewSolver, fVerbose );
    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        pAbc->pCex = Abc_CexCreate( 0, Abc_NtkPiNum(pNtk), pNtk->pModel, 0, 0, 0 );
    }
    pAbc->Status = RetValue;
    if ( !fSilent )
    {
        if ( RetValue == -1 )
            Abc_Print( 1, "UNDECIDED      " );
        else if ( RetValue == 0 )
            Abc_Print( 1, "SATISFIABLE    " );
        else
            Abc_Print( 1, "UNSATISFIABLE  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsat [-CILDE num] [-pansvh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    Abc_Print( -2, "\t         derives CNF from the current network and leaves it unchanged\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-L num : starting value for learned clause removal [default = %d]\n", nLearnedStart );
    Abc_Print( -2, "\t-D num : delta value for learned clause removal [default = %d]\n", nLearnedDelta );
    Abc_Print( -2, "\t-E num : ratio percentage for learned clause removal [default = %d]\n", nLearnedPerce );
    Abc_Print( -2, "\t-p     : align polarity of SAT variables [default = %s]\n", fAlignPol? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle ANDing/ORing of miter outputs [default = %s]\n", fAndOuts? "ANDing": "ORing" );
    Abc_Print( -2, "\t-n     : toggle using new solver [default = %s]\n", fNewSolver? "yes": "no" );
    Abc_Print( -2, "\t-s     : enable silent computation (no reporting) [default = %s]\n", fSilent? "yes": "no" );
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
int Abc_CommandXSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    abctime clk;
    int c;
    int fVerbose   = 0;
    int nConfLimit = 0;
    int nInsLimit  = 0;
    int nLearnedStart = 0;
    int nLearnedDelta = 0;
    int nLearnedPerce = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CILDEhv" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedStart < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedDelta < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nLearnedPerce = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLearnedPerce < 0 )
                goto usage;
            break;
        case 'h':
            goto usage;
        case 'v':
            fVerbose ^= 1;
            break;

        default:
            goto usage;
        }
    }

    if ( argc == globalUtilOptind + 1 )
    {
        char * pFileName = argv[globalUtilOptind];
        xSAT_Solver_t * p;
        int status;

        FILE * pFile = fopen( pFileName, "rb" );
        if ( pFile == NULL )
        {
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
            return 0;
        }
        xSAT_SolverParseDimacs( pFile, &p );

        clk = Abc_Clock();
        status = xSAT_SolverSolve( p );
        fclose( pFile );

        xSAT_SolverPrintStats( p );
        if ( status == 0 )
            Abc_Print( 1, "UNDECIDED      " );
        else if ( status == 1 )
            Abc_Print( 1, "SATISFIABLE    " );
        else
            Abc_Print( 1, "UNSATISFIABLE  " );

        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

        xSAT_SolverDestroy( p );
        return 0;
    }

usage:
    Abc_Print( -2, "usage: xsat [-CILDE num] [-hv]<file>.cnf\n" );
    Abc_Print( -2, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    Abc_Print( -2, "\t         derives CNF from the current network and leaves it unchanged\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-L num : starting value for learned clause removal [default = %d]\n", nLearnedStart );
    Abc_Print( -2, "\t-D num : delta value for learned clause removal [default = %d]\n", nLearnedDelta );
    Abc_Print( -2, "\t-E num : ratio percentage for learned clause removal [default = %d]\n", nLearnedPerce );
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
int Abc_CommandSatoko( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern satoko_opts_t * Cmd_DeriveOptionFromSettings( int argc, char ** argv );

    // create default options
    satoko_opts_t opts, * popts;
    satoko_default_opts(&opts);

    // override default options
    popts = Cmd_DeriveOptionFromSettings( argc, argv );
    if ( popts == NULL )
        goto usage;
    memcpy( &opts, popts, sizeof(satoko_opts_t) );
    ABC_FREE( popts );

    if ( argc == globalUtilOptind + 1 )
    {
        abctime clk;
        char * pFileName = argv[globalUtilOptind];
        satoko_t * p;
        int status;

        status = satoko_parse_dimacs( pFileName, &p );
        satoko_configure(p, &opts);

        clk = Abc_Clock();
        if ( status == SATOKO_OK )
            status = satoko_solve( p );

        if ( status == SATOKO_UNDEC )
            Abc_Print( 1, "UNDECIDED      " );
        else if ( status == SATOKO_SAT )
            Abc_Print( 1, "SATISFIABLE    " );
        else
            Abc_Print( 1, "UNSATISFIABLE  " );

        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

        satoko_destroy( p );
        return 0;
    }

usage:
#ifdef SATOKO_ACT_VAR_FIXED
    Abc_Print( -2, "usage: satoko [-CPDEFGHIJKLMNOQRSTU num] [-hv]<file>.cnf\n" );
#else
    Abc_Print( -2, "usage: satoko [-CPDEFGHIJKLMNOQRS num] [-hv]<file>.cnf\n" );
#endif
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", opts.conf_limit );
    Abc_Print( -2, "\t-P num : limit on the number of propagations [default = %d]\n", opts.conf_limit );
    Abc_Print( -2, "\n\tConstants used for restart heuristic:\n");
    Abc_Print( -2, "\t-D num : Constant value used by restart heuristics in forcing restarts [default = %f]\n", opts.f_rst );
    Abc_Print( -2, "\t-E num : Constant value used by restart heuristics in  blocking restarts [default = %f]\n", opts.b_rst );
    Abc_Print( -2, "\t-F num : Lower bound n.of conflicts for start blocking restarts [default = %d]\n", opts.fst_block_rst );
    Abc_Print( -2, "\t-G num : Size of the moving avarege queue for LBD (force restart) [default = %d]\n", opts.sz_lbd_bqueue );
    Abc_Print( -2, "\t-H num : Size of the moving avarege queue for Trail size (block restart) [default = %d]\n", opts.sz_trail_bqueue );
    Abc_Print( -2, "\n\tConstants used for clause database reduction heuristic:\n");
    Abc_Print( -2, "\t-I num : N.of conflicts before first clause databese reduction [default = %d]\n", opts.n_conf_fst_reduce );
    Abc_Print( -2, "\t-J num : Increment to reduce [default = %d]\n", opts.inc_reduce );
    Abc_Print( -2, "\t-K num : Special increment to reduce [default = %d]\n", opts.inc_special_reduce );
    Abc_Print( -2, "\t-L num : Protecs clauses from deletion for one turn if its LBD is lower [default = %d]\n", opts.lbd_freeze_clause );
    Abc_Print( -2, "\t-M num : Percentage of learned clauses to remove [default = %d]\n", ( int )( 100 * opts.learnt_ratio ) );
    Abc_Print( -2, "\t-N num : Max percentage of garbage in clause database [default = %d]\n", ( int )( 100 * opts.garbage_max_ratio ) );
    Abc_Print( -2, "\n\tConstants used for binary resolution (clause minimization):\n");
    Abc_Print( -2, "\t-O num : Max clause size for binary resolution [default = %d]\n", opts.clause_max_sz_bin_resol );
    Abc_Print( -2, "\t-Q num : Min clause LBD for binary resolution [default = %d]\n", opts.clause_min_lbd_bin_resol );
    Abc_Print( -2, "\n\tConstants used for branching (VSIDS heuristic):\n");
    Abc_Print( -2, "\t-R num : Clause activity decay factor (when using float clause activity) [default = %f]\n", opts.clause_decay );
    Abc_Print( -2, "\t-S num : Variable activity decay factor [default = %f]\n", opts.var_decay );
#ifdef SATOKO_ACT_VAR_FIXED
    Abc_Print( -2, "\t-T num : Variable activity limit valeu [default = 0x%08X]\n", opts.var_act_limit );
    Abc_Print( -2, "\t-U num : Variable activity re-scale factor [default = 0x%08X]\n", opts.var_act_rescale );
#endif
    Abc_Print( -2, "\n\t-v     : prints verbose information [default = %s]\n", opts.verbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Satoko( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSatokoDimacs( char * pFileName, satoko_opts_t * opts );
    extern void Gia_ManSatokoCall( Gia_Man_t * p, satoko_opts_t * opts, int fSplit, int fIncrem );
    int c, fSplit = 0, fIncrem = 0;

    satoko_opts_t opts;
    satoko_default_opts(&opts);
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Csivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            opts.conf_limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( opts.conf_limit < 0 )
                goto usage;
            break;
        case 's':
            fSplit ^= 1;
            break;
        case 'i':
            fIncrem ^= 1;
            break;
        case 'v':
            opts.verbose ^= 1;
            break;
        case 'h':
            goto usage;

        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 1 )
    {
        Gia_ManSatokoDimacs( argv[globalUtilOptind], &opts );
        return 0;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Satoko(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManSatokoCall( pAbc->pGia, &opts, fSplit, fIncrem );
    return 0;

usage:
    Abc_Print( -2, "usage: &satoko [-C num] [-sivh] <file.cnf>\n" );
    Abc_Print( -2, "\t             run Satoko by Bruno Schmitt\n" );
    Abc_Print( -2, "\t-C num     : limit on the number of conflicts [default = %d]\n", opts.conf_limit );
    Abc_Print( -2, "\t-s         : split multi-output miter into individual outputs [default = %s]\n", fSplit? "yes": "no" );
    Abc_Print( -2, "\t-i         : split multi-output miter and solve incrementally [default = %s]\n", fIncrem? "yes": "no" );
    Abc_Print( -2, "\t-v         : prints verbose information [default = %s]\n", opts.verbose? "yes": "no" );
    Abc_Print( -2, "\t<file.cnf> : (optional) CNF file to solve\n");
    Abc_Print( -2, "\t-h         : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sat3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManSat3Call( Gia_Man_t * p, int fSplit );
    int c, fSplit = 0, fIncrem = 0;

    satoko_opts_t opts;
    satoko_default_opts(&opts);
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Csivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            opts.conf_limit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( opts.conf_limit < 0 )
                goto usage;
            break;
        case 's':
            fSplit ^= 1;
            break;
        case 'i':
            fIncrem ^= 1;
            break;
        case 'v':
            opts.verbose ^= 1;
            break;
        case 'h':
            goto usage;

        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sat3(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManSat3Call( pAbc->pGia, fSplit );
    return 0;

usage:
    Abc_Print( -2, "usage: &sat3 [-C num] [-sivh]\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", opts.conf_limit );
    Abc_Print( -2, "\t-s     : split multi-output miter into individual outputs [default = %s]\n", fSplit? "yes": "no" );
    Abc_Print( -2, "\t-i     : split multi-output miter and solve incrementally [default = %s]\n", fIncrem? "yes": "no" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", opts.verbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Kissat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Mf_ManDumpCnf( Gia_Man_t * p, char * pFileName, int nLutSize, int fCnfObjIds, int fAddOrCla, int fVerbose );
    extern void Gia_ManKissatCall( Abc_Frame_t * pAbc, char * pFileName, char * pArgs, int nConfs, int nTimeLimit, int fSat, int fUnsat, int fPrintCex, int fVerbose );
    int c, nConfs = 0, nTimeLimit = 0, fSat = 0, fUnsat = 0, fPrintCex = 0, fKissat = 1, fVerbose = 0;
    char * pArgs = NULL;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTAsuckvh" ) ) != EOF )
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
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeLimit < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a file name.\n" );
                goto usage;
            }
            pArgs = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 's':
            fSat ^= 1;
            break;
        case 'u':
            fUnsat ^= 1;
            break;
        case 'c':
            fPrintCex ^= 1;
            break;
        case 'k':
            fKissat ^= 1;
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
    if ( argc == globalUtilOptind + 1 )
    {
        Gia_ManKissatCall( pAbc, argv[globalUtilOptind], pArgs, nConfs, nTimeLimit, fSat, fUnsat, fPrintCex, fVerbose );
        return 0;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Satoko(): There is no AIG.\n" );
        return 1;
    }
    else if ( fKissat )
    {
        extern Vec_Int_t * kissat_solve_cnf( Cnf_Dat_t * pCnf, char * pArgs, int nConfs, int nTimeLimit, int fSat, int fUnsat, int fPrintCex, int fVerbose );
        extern void * Mf_ManGenerateCnf( Gia_Man_t * pGia, int nLutSize, int fCnfObjIds, int fAddOrCla, int fMapping, int fVerbose );
        int nLutSize    = 8;
        int fCnfObjIds  = 0;        
        int fAddOrCla   = 1;
        Cnf_Dat_t * pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pAbc->pGia, nLutSize, fCnfObjIds, fAddOrCla, 0, fVerbose );
        Vec_Int_t * vRes = kissat_solve_cnf( pCnf, pArgs, nConfs, nTimeLimit, fSat, fUnsat, fPrintCex, 1 );
        Vec_IntFreeP( &vRes );
        Cnf_DataFree(pCnf);
    }
    else
    {
        int nLutSize    = 8;
        int fCnfObjIds  = 0;
        int fAddOrCla   = 1;
        char * pFileName = "_temp_.cnf";
        Mf_ManDumpCnf( pAbc->pGia, pFileName, nLutSize, fCnfObjIds, fAddOrCla, fVerbose );
        Gia_ManKissatCall( pAbc, pFileName, pArgs, nConfs, nTimeLimit, fSat, fUnsat, fPrintCex, fVerbose );
        unlink( pFileName );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &kissat [-CT num] [-suckvh] [-A string] <file.cnf>\n" );
    Abc_Print( -2, "\t             run SAT solver Kissat 4.0.2, by Armin Biere (https://github.com/arminbiere/kissat)\n" );
    Abc_Print( -2, "\t-C num     : limit on the number of conflicts [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-T num     : runtime limit in seconds [default = %d]\n", nTimeLimit );
    Abc_Print( -2, "\t-s         : expect a satisfiable problem [default = %s]\n", fSat ? "yes": "no" );
    Abc_Print( -2, "\t-u         : expect an unsatisfiable problem [default = %s]\n", fUnsat ? "yes": "no" );
    Abc_Print( -2, "\t-c         : prints satisfying assignment if satisfiable [default = %s]\n", fPrintCex ? "yes": "no" );
    Abc_Print( -2, "\t-k         : calls Kissat through programmable APIs [default = %s]\n", fKissat ? "yes": "no" );
    Abc_Print( -2, "\t-v         : prints verbose information [default = %s]\n", fVerbose ? "yes": "no" );
    Abc_Print( -2, "\t-A num     : string containing additional command-line args for the Kissat binary [default = %s]\n", pArgs ? pArgs : "unused" );
    Abc_Print( -2, "\t             (in particular, <&kissat -A \"--help\"> prints all command-line args of Kissat)\n" );
    Abc_Print( -2, "\t<file.cnf> : (optional) CNF file to solve\n");
    Abc_Print( -2, "\t-h         : print the command usage\n");
    Abc_Print( -2, "\n\t             The solver was integrated into ABC by Yukio Miyasaka\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int RetValue;
    int c;
    int nAlgo;
    int nPartSize;
    int nConfPart;
    int nConfTotal;
    int fAlignPol;
    int fSynthesize;
    int fVerbose;
    abctime clk;

    extern int Abc_NtkPartitionedSat( Abc_Ntk_t * pNtk, int nAlgo, int nPartSize, int nConfPart, int nConfTotal, int fAlignPol, int fSynthesize, int fVerbose );
    // set defaults
    nAlgo       =        0;
    nPartSize   =    10000;
    nConfPart   =        0;
    nConfTotal  =  1000000;
    fAlignPol   =        1;
    fSynthesize =        0;
    fVerbose    =        1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "APCpsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nAlgo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nAlgo < 0 )
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
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfTotal = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfTotal < 0 )
                goto usage;
            break;
        case 'p':
            fAlignPol ^= 1;
            break;
        case 's':
            fSynthesize ^= 1;
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
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    clk = Abc_Clock();
    RetValue = Abc_NtkPartitionedSat( pNtk, nAlgo, nPartSize, nConfPart, nConfTotal, fAlignPol, fSynthesize, fVerbose );
    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        //int i;
        //Abc_Obj_t * pObj;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        // print model
//        Abc_NtkForEachPi( pNtk, pObj, i )
//        {
//            Abc_Print( -1, "%d", (int)(pNtk->pModel[i] > 0) );
//            if ( i == 70 )
//                break;
//        }
//        Abc_Print( -1, "\n" );
    }

    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return 0;

usage:
    Abc_Print( -2, "usage: psat [-APC num] [-psvh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using partitioning\n" );
    Abc_Print( -2, "\t         (derives CNF from the current network and leave it unchanged)\n" );
    Abc_Print( -2, "\t         for multi-output miters, tries to prove that the AND of POs is always 0\n" );
    Abc_Print( -2, "\t         (if POs should be ORed instead of ANDed, use command \"orpos\")\n" );
    Abc_Print( -2, "\t-A num : partitioning algorithm [default = %d]\n", nAlgo );
    Abc_Print( -2, "\t         0 : no partitioning\n" );
    Abc_Print( -2, "\t         1 : partitioning by level\n" );
    Abc_Print( -2, "\t         2 : DFS post-order\n" );
    Abc_Print( -2, "\t         3 : DFS pre-order\n" );
    Abc_Print( -2, "\t         4 : bit-slicing\n" );
    Abc_Print( -2, "\t         partitions are ordered by level (high level first)\n" );
    Abc_Print( -2, "\t-P num : limit on the partition size [default = %d]\n", nPartSize );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfTotal );
    Abc_Print( -2, "\t-p     : align polarity of SAT variables [default = %s]\n", fAlignPol? "yes": "no" );
    Abc_Print( -2, "\t-s     : apply logic synthesis to each partition [default = %s]\n", fSynthesize? "yes": "no" );
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
int Abc_CommandAbc9Sat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Int_t * Cbs2_ManSolveMiterNc( Gia_Man_t * pAig, int nConfs, Vec_Str_t ** pvStatus, int fVerbose );
    extern Vec_Int_t * Cbs3_ManSolveMiterNc( Gia_Man_t * pAig, int nConfs, int nRestarts, Vec_Str_t ** pvStatus, int fVerbose );
    Cec_ParSat_t ParsSat, * pPars = &ParsSat;
    Gia_Man_t * pTemp;
    int c;
    int fNewSolver = 0, fNewSolver2 = 0, fCSat = 0, f0Proved = 0, nRestarts = 1;
    Cec_ManSatSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "JCRSNanmtcxyzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->SolverType = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->SolverType < 0 )
                goto usage;
            break;
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRestarts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRestarts < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCallsRecycle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCallsRecycle < 0 )
                goto usage;
            break;
        case 'a':
            pPars->fSaveCexes ^= 1;
            break;
        case 'n':
            pPars->fNonChrono ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 't':
            pPars->fLearnCls ^= 1;
            break;
        case 'c':
            fCSat ^= 1;
            break;
        case 'x':
            fNewSolver ^= 1;
            break;
        case 'y':
            fNewSolver2 ^= 1;
            break;
        case 'z':
            f0Proved ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sat(): There is no AIG.\n" );
        return 1;
    }
    if ( fCSat )
    {
        Vec_Int_t * vCounters;
        Vec_Str_t * vStatus;
        if ( fNewSolver )
            vCounters = Cbs2_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        else if ( fNewSolver2 )
            vCounters = Cbs3_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, nRestarts, &vStatus, pPars->fVerbose );
        else if ( pPars->fLearnCls )
            vCounters = Tas_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        else if ( pPars->fNonChrono )
            vCounters = Cbs_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, &vStatus, f0Proved, pPars->fVerbose );
        else
            vCounters = Cbs_ManSolveMiter( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        Vec_IntFree( vCounters );
        Vec_StrFree( vStatus );
    }
    else
    {
        pTemp = Cec_ManSatSolving( pAbc->pGia, pPars, f0Proved );
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    if ( pAbc->pGia->vSeqModelVec )
    {
        Vec_Int_t * vStatuses = Abc_FrameDeriveStatusArray2( pAbc->pGia->vSeqModelVec );
        Abc_FrameReplacePoStatuses( pAbc, &vStatuses );
        Abc_FrameReplaceCexVec( pAbc, &pAbc->pGia->vSeqModelVec );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &sat [-JCRSN <num>] [-anmctxzvh]\n" );
    Abc_Print( -2, "\t         performs SAT solving for the combinational outputs\n" );
    Abc_Print( -2, "\t-J num : the SAT solver type [default = %d]\n", pPars->SolverType );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-R num : the max number of restarts at a node [default = %d]\n", nRestarts );
    Abc_Print( -2, "\t-S num : the min number of variables to recycle the solver [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-N num : the min number of calls to recycle the solver [default = %d]\n", pPars->nCallsRecycle );
    Abc_Print( -2, "\t-a     : toggle solving all outputs and saving counter-examples [default = %s]\n", pPars->fSaveCexes? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle using non-chronological backtracking [default = %s]\n", pPars->fNonChrono? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", fCSat? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using learning in curcuit-based solver [default = %s]\n", pPars->fLearnCls? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle using new solver [default = %s]\n", fNewSolver? "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle using new solver [default = %s]\n", fNewSolver2? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle replacing proved cones by const0 [default = %s]\n", f0Proved? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SatEnum( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManSatEnum( Gia_Man_t * p, int nConfLimit, int nTimeOut, int fVerbose );
    int c, nConfLimit = 0, nTimeOut = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SatEnum(): There is no AIG.\n" );
        return 1;
    }
    Gia_ManSatEnum( pAbc->pGia, nConfLimit, nTimeOut, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &satenum [-CT <num>] [-vh]\n" );
    Abc_Print( -2, "\t         enumerates solutions of the combinational miter\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-T num : global timeout [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",   fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SplitSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Cnf_SplitSat( char * pFileName, int iVarBeg, int iVarEnd, int nLits, int Value, int TimeOut, int nProcs, int nIters, int Seed, int fPrepro, int fVerbose );
    int c, iVarBeg = 0, iVarEnd = ABC_INFINITY, nLits = 10, Value = 2, TimeOut = 5, nProcs = 1, nIters = 1, Seed = 0, fPrepro = 0, fVerbose = 0; char * pFileName = NULL;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BENVTPISpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by a positive integer.\n" );
                goto usage;
            }
            iVarBeg = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVarBeg < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a positive integer.\n" );
                goto usage;
            }
            iVarEnd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVarEnd < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLits < 0 )
                goto usage;
            break;                                    
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Value = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Value < 0 || Value > 2 )
                goto usage;
            break;                  
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 )
                goto usage;
            break;
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
        case 'p':
            fPrepro ^= 1;
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
    // get the file name
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9SplitSat(): CNF file names should be given on the command line.\n" );
        return 1;
    }
    {        
        FILE * pFile;
        pFileName = argv[globalUtilOptind];
        pFile = fopen( pFileName, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open file \"%s\" with the input test patterns.\n", pFileName );
            return 0;
        }
        fclose( pFile );
    }
    Cnf_SplitSat( pFileName, iVarBeg, iVarEnd, nLits, Value, TimeOut, nProcs, nIters, Seed, fPrepro, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &splitsat [-BENVTPIS num] [-pvh]\n" );
    Abc_Print( -2, "\t         solves CNF-based SAT problem by randomized case-splitting\n" );
    Abc_Print( -2, "\t-B num : the first CNF variable to use for splitting [default = %d]\n",         iVarBeg );
    Abc_Print( -2, "\t-E num : the last CNF variable to use for splitting [default = %d]\n",          iVarEnd );
    Abc_Print( -2, "\t-N num : the number of CNF variables to use for splitting [default = %d]\n",    nLits );
    Abc_Print( -2, "\t-V num : the variable values to use (0, 1, or 2 for \"any\") [default = %d]\n", Value );
    Abc_Print( -2, "\t-T num : the runtime limit in seconds per subproblem [default = %d]\n",         TimeOut );
    Abc_Print( -2, "\t-P num : the number of concurrent processes [default = %d]\n",                  nProcs );
    Abc_Print( -2, "\t-I num : the max number of iterations (0 = infinity) [default = %d]\n",         nIters );
    Abc_Print( -2, "\t-S num : the random seed used to generate cofactors [default = %d]\n",          Seed );    
    Abc_Print( -2, "\t-p     : toggle using SatELIte (http://minisat.se/SatELite.html) [default = %s]\n", fPrepro? "yes": "no" );    
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",                 fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SatTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Bmc_LoadTest( Gia_Man_t * pGia, int fLoadCnf, int fVerbose );
    int c, fLoadCnf = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fLoadCnf ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9SatTest(): There is no AIG.\n" );
        return 0;
    }
    Bmc_LoadTest( pAbc->pGia, fLoadCnf, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &sattest [-cvh]\n" );
    Abc_Print( -2, "\t         performs testing of dynamic CNF loading\n" );
    Abc_Print( -2, "\t-c     : toggle dynamic CNF loading [default = %s]\n",          fLoadCnf? "yes": "no" );
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
int Abc_CommandAbc9Qbf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_QbfDumpFile( Gia_Man_t * pGia, int nPars );
    extern void Gia_QbfDumpFileInv( Gia_Man_t * pGia, int nPars );
    extern int Gia_QbfSolve( Gia_Man_t * pGia, int nPars, int nIterLimit, int nConfLimit, int nTimeOut, int nEncVars, int fGlucose, int fCadical, int fSilent, int fVerbose );
    int c, nPars   = -1;
    int nIterLimit =  0;
    int nConfLimit =  0;
    int nTimeOut   =  0;
    int nEncVars   =  0;
    int fDumpCnf   =  0;
    int fDumpCnf2  =  0;
    int fGlucose   =  0;
    int fCadical   =  0;
    int fSilent    =  0;
    int fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PICTKdegcsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPars < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIterLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIterLimit < 0 )
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
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nEncVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nEncVars < 0 )
                goto usage;
            break;
        case 'd':
            fDumpCnf ^= 1;
            break;
        case 'e':
            fDumpCnf2 ^= 1;
            break;
        case 'g':
            fGlucose ^= 1;
            break;
        case 'c':
            fCadical ^= 1;
            break;
        case 's':
            fSilent ^= 1;
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
    if ( Gia_ManRegNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Works only for combinational networks.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) != 1 )
    {
        Abc_Print( -1, "The miter should have one primary output.\n" );
        return 1;
    }
    if ( !(nPars > 0 && nPars < Gia_ManPiNum(pAbc->pGia)) )
    {
        Abc_Print( -1, "The number of parameter variables is invalid (should be > 0 and < PI num).\n" );
        return 1;
    }
    if ( fDumpCnf )
        Gia_QbfDumpFile( pAbc->pGia, nPars );
    else if ( fDumpCnf2 )
        Gia_QbfDumpFileInv( pAbc->pGia, nPars );
    else
        Gia_QbfSolve( pAbc->pGia, nPars, nIterLimit, nConfLimit, nTimeOut, nEncVars, fGlucose, fCadical, fSilent, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &qbf [-PICTK num] [-degcsvh]\n" );
    Abc_Print( -2, "\t         solves QBF problem EpVxM(p,x)\n" );
    Abc_Print( -2, "\t-P num : number of parameters p (should be the first PIs) [default = %d]\n", nPars );
    Abc_Print( -2, "\t-I num : quit after the given iteration even if unsolved [default = %d]\n", nIterLimit );
    Abc_Print( -2, "\t-C num : conflict limit per problem [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-T num : global timeout [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-K num : the number of input bits (for encoding miters only) [default = %d]\n", nEncVars );
    Abc_Print( -2, "\t-d     : toggle dumping QDIMACS file instead of solving (complemented QBF) [default = %s]\n", fDumpCnf? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle dumping QDIMACS file instead of solving (original QBF) [default = %s]\n", fDumpCnf2? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", fGlucose? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using CaDiCaL by Armin Biere [default = %s]\n", fCadical? "yes": "no" );
    Abc_Print( -2, "\t-s     : no printout except when a solution is found [default = %s]\n", fSilent? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n\n");
    Abc_Print( -2, "\t         As an example of using this command, consider specification (the three-input AND-gate) and implementation\n"); 
    Abc_Print( -2, "\t         (the circuit with function AND(XOR(x0, x1), x2)).  The problem is to check whether the output of the XOR (node n)\n"); 
    Abc_Print( -2, "\t         can be implemented differently, so that these two circuits are equivalent.  Obviously this can be done!\n");
    Abc_Print( -2, "\t         Simply replace XOR gate by AND gate.\n\n");
    Abc_Print( -2, "\t         > # file s2.blif\n");
    Abc_Print( -2, "\t         > .model and3\n");
    Abc_Print( -2, "\t         > .inputs x0 x1 x2 n\n");
    Abc_Print( -2, "\t         > .outputs F\n");
    Abc_Print( -2, "\t         > .names m x2 F\n");
    Abc_Print( -2, "\t         > 11 1\n");
    Abc_Print( -2, "\t         > .names x0 x1 m\n");
    Abc_Print( -2, "\t         > 11 1\n");
    Abc_Print( -2, "\t         > .end\n\n");
    Abc_Print( -2, "\t         > # file i2.blif\n");
    Abc_Print( -2, "\t         > .model impl\n");
    Abc_Print( -2, "\t         > .inputs x0 x1 x2 n\n");
    Abc_Print( -2, "\t         > .outputs F\n");
    Abc_Print( -2, "\t         > .names n x2 F\n");
    Abc_Print( -2, "\t         > 11 1\n");
    Abc_Print( -2, "\t         > #.names x0 x1 n\n");
    Abc_Print( -2, "\t         > #01 1\n");
    Abc_Print( -2, "\t         > #10 1\n");
    Abc_Print( -2, "\t         > .end\n\n");
    Abc_Print( -2, "\t         > abc 08> miter -n i2.blif s2.blif; ps\n");
    Abc_Print( -2, "\t         > impl_and3_miter               : i/o =    4/    1  lat =    0  and =      6  lev =  4\n");
    Abc_Print( -2, "\t         > abc 09> &get; &qbf -P 3\n");
    Abc_Print( -2, "\t         > The problem is UNSAT after 1 iterations.  Time =     0.00 sec\n\n");
    Abc_Print( -2, "\t         UNSAT here means that the ECO solution with the given rectification point *has* a solution.\n\n");
    Abc_Print( -2, "\t         For more info, refer to Figure 1 in the following paper A. Q. Dao, N.-Z. Lee, L.-C. Chen, M. P.-H. Lin,\n");
    Abc_Print( -2, "\t         J.-H. R. Jiang, A. Mishchenko, and R. Brayton, \"Efficient computation of ECO patch functions\", Proc. DAC'18.\n");
    Abc_Print( -2, "\t         https://people.eecs.berkeley.edu/~alanmi/publications/2018/dac18_eco.pdf\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9HomoQbf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_Gen2CreateMiter( int nLutSize, int nLutNum );
    int nLutSize  =  2;
    int nLutNum   =  3;
    int fVerbose  =  0;
    int c;
    Gia_Man_t * pTemp;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pTemp = Gia_Gen2CreateMiter( nLutSize, nLutNum );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &homoqbf [-KN num] [-vh]\n" );
    Abc_Print( -2, "\t         generates QBF miter for the encoding problem\n" );
    Abc_Print( -2, "\t-K num : the LUT size [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-N num : the number of LUTs [default = %d]\n", nLutNum );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
