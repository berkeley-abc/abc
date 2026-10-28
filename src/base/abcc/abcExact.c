/**CFile****************************************************************

  FileName    [abcExact.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Exact synthesis.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "bool/kit/kit.h"
#include "sat/bmc/bmc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandExact                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmsStart               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmsStop                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmsPs                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMajExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTwoExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandCasExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAndExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAllExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTopoExact              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNetExact               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestExact              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMajGen                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Exmap              ( Abc_Frame_t * pAbc, int argc, char ** argv );



/**Function*************************************************************

  Synopsis    [Registers exact synthesis commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitExact( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Synthesis",    "exact",         Abc_CommandExact,            1 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "bms_start",  Abc_CommandBmsStart,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "bms_stop",   Abc_CommandBmsStop,          0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "bms_ps",     Abc_CommandBmsPs,            0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "majexact",   Abc_CommandMajExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "twoexact",   Abc_CommandTwoExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "lutexact",   Abc_CommandLutExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "casexact",   Abc_CommandCasExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "andexact",   Abc_CommandAndExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "allexact",   Abc_CommandAllExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "topoexact",  Abc_CommandTopoExact,        0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "netexact",   Abc_CommandNetExact,         0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "testexact",  Abc_CommandTestExact,        0 );
    Cmd_CommandAdd( pAbc, "Exact synthesis", "majgen",     Abc_CommandMajGen,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&exmap",        Abc_CommandAbc9Exmap,        0 );
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
int Abc_CommandExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManFindExact( word * pTruth, int nVars, int nFunc, int nMaxDepth, int * pArrivalTimes, int nBTLimit, int nStartGates, int fVerbose );

    int c, nMaxDepth = -1, fMakeAIG = 0, fTest = 0, fVerbose = 0, nVars = 0, nVarsTmp, nFunc = 0, nStartGates = 1, nBTLimit = 400000;
    char * p1, * p2;
    word pTruth[64];
    int pArrTimeProfile[8], fHasArrTimeProfile = 0;
    Abc_Ntk_t * pNtkRes;
    Gia_Man_t * pGiaRes;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "DASCatvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxDepth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxDepth < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            fHasArrTimeProfile = 1;
            p1 = p2 = argv[globalUtilOptind++];
            while ( true ) {
                if ( *p2 == ',' )
                {
                    if ( nVars >= 8 )
                        goto usage;
                    *p2 = '\0';
                    pArrTimeProfile[nVars++] = atoi( p1 );
                    *p2++ = ',';
                    p1 = p2;
                }
                else if ( *p2 == '\0' )
                {
                    if ( nVars >= 8 )
                        goto usage;
                    pArrTimeProfile[nVars++] = atoi( p1 );
                    break;
                }
                else
                    ++p2;
            }
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStartGates = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStartGates < 1 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'a':
            fMakeAIG ^= 1;
            break;
        case 't':
            fTest ^= 1;
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

    if ( fTest )
    {
        extern void Abc_ExactTest( int fVerbose );
        extern void Abc_ExactStoreTest( int fVerbose );

        printf( "run test suite, ignore all other settings\n" );
        Abc_ExactTest( fVerbose );
        Abc_ExactStoreTest( fVerbose );
        return 0;
    }

    if ( argc == globalUtilOptind )
        goto usage;

    memset( pTruth, 0, 64 * sizeof(word) );
    while ( globalUtilOptind < argc )
    {
        if ( nFunc == 16 )
        {
            Abc_Print( -1, "Too many functions (at most 16 supported).\n" );
            goto usage;
        }
        nVarsTmp = Abc_TtReadHex( &pTruth[nFunc << 2], argv[globalUtilOptind++] );
        nFunc++;
        if ( nVars == 0 )
            nVars = nVarsTmp;
        else if ( nVars > 8 )
        {
            Abc_Print( -1, "Only 8-variable functions are supported.\n" );
            goto usage;
        }
        else if ( nVars != nVarsTmp )
        {
            Abc_Print( -1, "All functions need to have the same size.\n" );
            goto usage;
        }
    }

    if ( fMakeAIG )
    {
        pGiaRes = Gia_ManFindExact( pTruth, nVars, nFunc, nMaxDepth, fHasArrTimeProfile ? pArrTimeProfile : NULL, nBTLimit, nStartGates - 1, fVerbose );
        if ( pGiaRes )
            Abc_FrameUpdateGia( pAbc, pGiaRes );
        else
            Abc_Print( 0, "Could not find AIG within given resource constraints, retry with different value for -C.\n" );
    }
    else
    {
        pNtkRes = Abc_NtkFindExact( pTruth, nVars, nFunc, nMaxDepth, fHasArrTimeProfile ? pArrTimeProfile : NULL, nBTLimit, nStartGates - 1, fVerbose );
        if ( pNtkRes )
        {
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
            Abc_FrameClearVerifStatus( pAbc );
        }
        else
            Abc_Print( 0, "Could not find network within given resource constraints, retry with different value for -C.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: exact [-DSC <num>] [-A <list>] [-atvh] <truth1> <truth2> ...\n" );
    Abc_Print( -2, "\t           finds optimum networks using SAT-based exact synthesis for hex truth tables <truth1> <truth2> ...\n" );
    Abc_Print( -2, "\t-D <num>  : constrain maximum depth (if too low, algorithm may not terminate)\n" );
    Abc_Print( -2, "\t-A <list> : input arrival times (comma separated list)\n" );
    Abc_Print( -2, "\t-S <num>  : number of start gates in search [default = %d]\n", nStartGates );
    Abc_Print( -2, "\t-C <num>  : the limit on the number of conflicts; turn off with 0 [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-a        : toggle create AIG [default = %s]\n", fMakeAIG ? "yes" : "no" );
    Abc_Print( -2, "\t-t        : run test suite\n" );
    Abc_Print( -2, "\t-v        : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h        : print the command usage\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t            This command was contributed by Mathias Soeken from EPFL in July 2016.\n" );
    Abc_Print( -2, "\t            The author can be contacted as mathias.soeken at epfl.ch\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmsStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_ExactIsRunning();
    extern void Abc_ExactStart( int nBTLimit, int fMakeAIG, int fVerbose, int fVeryVerbose, const char *pFilename );

    int c, fMakeAIG = 0, fVerbose = 0, fVeryVerbose = 0, nBTLimit = 100;
    char * pFilename = NULL;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cavwh" ) ) != EOF )
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
            break;
        case 'a':
            fMakeAIG ^= 1;
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

    if ( argc > globalUtilOptind )
    {
        pFilename = argv[globalUtilOptind++];
    }

    if ( Abc_ExactIsRunning() )
    {
        Abc_Print( -1, "BMS manager is already started." );
        return 1;
    }

    Abc_ExactStart( nBTLimit, fMakeAIG, fVerbose, fVeryVerbose, pFilename );
    return 0;

usage:
    Abc_Print( -2, "usage: bms_start [-C <num>] [-avwh] [<file>]\n" );
    Abc_Print( -2, "\t           starts BMS manager for recording optimum networks\n" );
    Abc_Print( -2, "\t           if <file> is specified, store entries are read from that file\n" );
    Abc_Print( -2, "\t-C <num> : the limit on the number of conflicts [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-a       : toggle create AIG [default = %s]\n", fMakeAIG ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-w       : toggle very verbose printout [default = %s]\n", fVeryVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Mathias Soeken from EPFL in July 2016.\n" );
    Abc_Print( -2, "\t           The author can be contacted as mathias.soeken at epfl.ch\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmsStop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_ExactIsRunning();
    extern void Abc_ExactStop( const char *pFilename );

    int c;
    char * pFilename = NULL;

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

    if ( argc > globalUtilOptind )
    {
        pFilename = argv[globalUtilOptind++];
    }

    if ( !Abc_ExactIsRunning() )
    {
        Abc_Print( -1, "BMS manager is not started." );
        return 1;
    }

    Abc_ExactStop( pFilename );
    return 0;

usage:
    Abc_Print( -2, "usage: bms_stop [-C <num>] [-vh] [<file>]\n" );
    Abc_Print( -2, "\t           stops BMS manager for recording optimum networks\n" );
    Abc_Print( -2, "\t           if <file> is specified, store entries are written to that file\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Mathias Soeken from EPFL in July 2016.\n" );
    Abc_Print( -2, "\t           The author can be contacted as mathias.soeken at epfl.ch\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmsPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_ExactIsRunning();
    extern void Abc_ExactStats();

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

    if ( !Abc_ExactIsRunning() )
    {
        Abc_Print( -1, "BMS manager is not started." );
        return 1;
    }

    Abc_ExactStats();
    return 0;

usage:
    Abc_Print( -2, "usage: bms_ps [-h]\n" );
    Abc_Print( -2, "\t           shows statistics about BMS manager\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Mathias Soeken from EPFL in July 2016.\n" );
    Abc_Print( -2, "\t           The author can be contacted as mathias.soeken at epfl.ch\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMajExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Maj_ManExactSynthesis( int nVars, int nNodes, int fUseConst, int fUseLine, int fVerbose );
    extern int Maj_ManExactSynthesis2( int nVars, int nNodes, int fUseConst, int fUseLine, int fUseRand, int nRands, int fVerbose );
    int c, nVars = 3, nNodes = 1, fUseConst = 0, fUseLine = 0, fGlucose = 0, fUseRand = 0, nRands = 0, fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "INRfcrgvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 )
                goto usage;
            break;
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRands < 0 )
                goto usage;
            break;
        case 'f':
            fUseConst ^= 1;
            break;
        case 'c':
            fUseLine ^= 1;
            break;
        case 'r':
            fUseRand ^= 1;
            break;
        case 'g':
            fGlucose ^= 1;
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
    if ( (nVars & 1) == 0 )
    {
        Abc_Print( -1, "Cannot sythesize MAJ gate with an even number of inputs (%d).\n", nVars );
        return 1;
    }
    if ( fGlucose )
        Maj_ManExactSynthesis( nVars, nNodes, fUseConst, fUseLine, fVerbose );
    else
        Maj_ManExactSynthesis2( nVars, nNodes, fUseConst, fUseLine, fUseRand, nRands, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: majexact [-INR <num>] [-fcrgvh]\n" );
    Abc_Print( -2, "\t           exact synthesis of multi-input MAJ using MAJ3 gates\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-N <num> : the number of MAJ3 nodes [default = %d]\n", nNodes );
    Abc_Print( -2, "\t-R <num> : the number of additional connections [default = %d]\n", nRands );
    Abc_Print( -2, "\t-f       : toggle using constant fanins [default = %s]\n", fUseConst ? "yes" : "no" );
    Abc_Print( -2, "\t-c       : toggle using cascade topology [default = %s]\n", fUseLine ? "yes" : "no" );
    Abc_Print( -2, "\t-r       : toggle using random topology [default = %s]\n", fUseRand ? "yes" : "no" );
    Abc_Print( -2, "\t-g       : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", fGlucose ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermAddFanin( int * pFans, int iNode, int iFanin )
{
    int * pNode = pFans + 2 * iNode;
    if ( pNode[0] == iFanin || pNode[1] == iFanin )
        return 0;
    if ( pNode[0] == -1 && pNode[1] == -1 )
        pNode[Abc_Random(0) & 1] = iFanin;
    else if ( pNode[0] == -1 )
        pNode[0] = iFanin;
    else if ( pNode[1] == -1 )
        pNode[1] = iFanin;
    else
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Records a required fanin in the topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermAddRequired( int * pFans, int nVars, int nNodes, int iFanin )
{
    int iNodeStart = (iFanin + 1 > nVars) ? iFanin + 1 - nVars : 0;
    int i, nChoices = 0, iChoice = -1;
    for ( i = iNodeStart; i < nNodes; i++ )
    {
        int * pNode = pFans + 2 * i;
        if ( pNode[0] == iFanin || pNode[1] == iFanin )
            continue;
        if ( pNode[0] != -1 && pNode[1] != -1 )
            continue;
        if ( Abc_Random(0) % ++nChoices == 0 )
            iChoice = i;
    }
    return iChoice >= 0 && Abc_TwoExactPermAddFanin( pFans, iChoice, iFanin );
}

/**Function*************************************************************

  Synopsis    [Counts distinct fanins in the topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermCountDistinct( int * pFans, int nVars, int iNode )
{
    int iPrevObj = nVars + iNode - 1;
    int pVals[4], nVals = 0, i, k;
    assert( iNode > 0 );
    for ( i = iNode - 1; i <= iNode; i++ )
    for ( k = 0; k < 2; k++ )
    {
        int v = pFans[2 * i + k];
        int j, fSeen = 0;
        if ( v == iPrevObj )
            continue;
        for ( j = 0; j < nVals; j++ )
            fSeen |= pVals[j] == v;
        if ( !fSeen )
            pVals[nVals++] = v;
    }
    return nVals;
}

/**Function*************************************************************

  Synopsis    [Checks the topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermCheck( int * pFans, int nVars, int nNodes, int fStrict )
{
    int nObjs = nVars + nNodes;
    int * pUsed = ABC_CALLOC( int, nObjs );
    int i, RetValue = 1;
    for ( i = 0; i < nNodes; i++ )
    {
        if ( pFans[2*i] < 0 || pFans[2*i+1] < 0 || pFans[2*i] >= nVars + i || pFans[2*i+1] >= nVars + i || pFans[2*i] == pFans[2*i+1] )
            RetValue = 0;
        if ( fStrict && i > 0 && Abc_TwoExactPermCountDistinct(pFans, nVars, i) < 3 )
            RetValue = 0;
        if ( !RetValue )
            break;
        pUsed[pFans[2*i]]++;
        pUsed[pFans[2*i+1]]++;
    }
    if ( RetValue )
        for ( i = 0; i < nObjs - 1; i++ )
            if ( pUsed[i] == 0 )
            {
                RetValue = 0;
                break;
            }
    ABC_FREE( pUsed );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Encodes the topology constraints as a string.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Abc_TwoExactPermEncode( int * pFans, int nVars, int nNodes )
{
    char * pPerm = ABC_ALLOC( char, 3 * nNodes );
    int i, k, Pos = 0;
    for ( i = 0; i < nNodes; i++ )
    {
        if ( i )
            pPerm[Pos++] = '_';
        for ( k = 0; k < 2; k++ )
            pPerm[Pos++] = pFans[2*i+k] >= 0 && pFans[2*i+k] < nVars ? 'a' + pFans[2*i+k] : '*';
    }
    pPerm[Pos] = 0;
    return pPerm;
}

/**Function*************************************************************

  Synopsis    [Formats the name of an input or internal object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Abc_TwoExactObjName( int iObj, int nVars, char * pBuffer )
{
    if ( iObj < 0 )
        sprintf( pBuffer, "*" );
    else if ( iObj < nVars )
        sprintf( pBuffer, "%c", 'a' + iObj );
    else if ( iObj - nVars < 26 )
        sprintf( pBuffer, "%c", 'A' + iObj - nVars );
    else
        sprintf( pBuffer, "N%d", iObj - nVars );
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    [Encodes a fully specified topology.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Abc_TwoExactPermEncodeFull( int * pFans, int nVars, int nNodes )
{
    int nSize = 8 * (nNodes + 1);
    char * pPerm = ABC_ALLOC( char, nSize );
    int i, k, Pos = 0;
    char Name[16];
    for ( i = 0; i < nNodes; i++ )
    {
        if ( i )
            pPerm[Pos++] = '_';
        for ( k = 0; k < 2; k++ )
            Pos += sprintf( pPerm + Pos, "%s", Abc_TwoExactObjName(pFans[2*i+k], nVars, Name) );
    }
    pPerm[Pos] = 0;
    return pPerm;
}

/**Function*************************************************************

  Synopsis    [Parses an object name in the topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermParseObj( char ** ppToken, int nVars, int nNodes, int * pObj )
{
    char * pToken = *ppToken;
    if ( *pToken == '*' )
    {
        *pObj = -1;
        *ppToken = pToken + 1;
        return 1;
    }
    if ( *pToken >= 'a' && *pToken < 'a' + nVars )
    {
        *pObj = *pToken - 'a';
        *ppToken = pToken + 1;
        return 1;
    }
    if ( *pToken >= 'A' && *pToken <= 'Z' )
    {
        *pObj = nVars + *pToken - 'A';
        *ppToken = pToken + 1;
        return *pObj < nVars + nNodes;
    }
    if ( *pToken == 'N' )
    {
        char * pNext = pToken + 1;
        int Num = 0;
        if ( *pNext < '0' || *pNext > '9' )
            return 0;
        while ( *pNext >= '0' && *pNext <= '9' )
            Num = 10 * Num + *pNext++ - '0';
        *pObj = nVars + Num;
        *ppToken = pNext;
        return *pObj < nVars + nNodes;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Adds unspecified fanins to the topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactPermAddDcs( int * pFans, int nVars, int nNodes, int nDcs, int nSkip, int fAll )
{
    int i, k, nLetters = 0;
    if ( nDcs == 0 )
        return 1;
    for ( i = nSkip; i < 2 * nNodes; i++ )
        nLetters += pFans[i] >= 0 && (fAll || pFans[i] < nVars);
    if ( nDcs > nLetters )
        return 0;
    for ( k = 0; k < nDcs; k++ )
    {
        int iChoice = -1, nChoices = 0;
        for ( i = nSkip; i < 2 * nNodes; i++ )
            if ( pFans[i] >= 0 && (fAll || pFans[i] < nVars) && Abc_Random(0) % ++nChoices == 0 )
                iChoice = i;
        assert( iChoice >= 0 );
        pFans[iChoice] = -1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Generates random topology constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int * Abc_TwoExactPermRandom( int nVars, int nNodes, int nDcs )
{
    int nObjs = nVars + nNodes;
    int Attempt, i, k;
    for ( Attempt = 0; Attempt < 200; Attempt++ )
    {
        int * pFans = ABC_ALLOC( int, 2 * nNodes );
        int fOk = 1;
        for ( i = 0; i < 2 * nNodes; i++ )
            pFans[i] = -1;
        for ( i = nObjs - 2; i >= nVars && fOk; i-- )
            fOk = Abc_TwoExactPermAddRequired( pFans, nVars, nNodes, i );
        for ( i = 0; i < nVars && fOk; i++ )
            fOk = Abc_TwoExactPermAddRequired( pFans, nVars, nNodes, i );
        for ( i = 0; i < nNodes && fOk; i++ )
        {
            int Limit = nVars + i;
            for ( k = 0; k < 2; k++ )
            {
                int Try;
                if ( pFans[2*i+k] != -1 )
                    continue;
                for ( Try = 0; Try < 100; Try++ )
                    if ( Abc_TwoExactPermAddFanin( pFans, i, Abc_Random(0) % Limit ) )
                        break;
                if ( Try == 100 )
                    fOk = 0;
            }
            if ( pFans[2*i] > pFans[2*i+1] )
                ABC_SWAP( int, pFans[2*i], pFans[2*i+1] );
        }
        if ( fOk && Abc_TwoExactPermCheck(pFans, nVars, nNodes, 1) && Abc_TwoExactPermAddDcs(pFans, nVars, nNodes, nDcs, 0, 0) )
            return pFans;
        ABC_FREE( pFans );
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Generates topology constraints from a seed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int * Abc_TwoExactPermRandomSeeded( int nVars, int nNodes, int nDcs, Vec_Int_t * vSeedPairs, int nSeeds )
{
    int nObjs = nVars + nNodes;
    int Attempt, i, k;
    nSeeds = Abc_MinInt( nSeeds, Vec_IntSize(vSeedPairs) );
    for ( Attempt = 0; Attempt < 200; Attempt++ )
    {
        int * pFans = ABC_ALLOC( int, 2 * nNodes );
        int * pUsed = ABC_CALLOC( int, Vec_IntSize(vSeedPairs) );
        int fOk = 1;
        for ( i = 0; i < 2 * nNodes; i++ )
            pFans[i] = -1;
        for ( i = 0; i < nSeeds; i++ )
        {
            int s, iSeed = -1, nChoices = 0;
            for ( s = 0; s < Vec_IntSize(vSeedPairs); s++ )
                if ( !pUsed[s] && Abc_Random(0) % ++nChoices == 0 )
                    iSeed = s;
            assert( iSeed >= 0 );
            pUsed[iSeed] = 1;
            int Pair = Vec_IntEntry( vSeedPairs, iSeed );
            pFans[2*i]   = Pair / nVars;
            pFans[2*i+1] = Pair % nVars;
        }
        for ( i = nObjs - 2; i >= nVars && fOk; i-- )
            fOk = Abc_TwoExactPermAddRequired( pFans, nVars, nNodes, i );
        for ( i = 0; i < nVars && fOk; i++ )
            fOk = Abc_TwoExactPermAddRequired( pFans, nVars, nNodes, i );
        for ( i = 0; i < nNodes && fOk; i++ )
        {
            int Limit = nVars + i;
            for ( k = 0; k < 2; k++ )
            {
                int Try;
                if ( pFans[2*i+k] != -1 )
                    continue;
                for ( Try = 0; Try < 100; Try++ )
                    if ( Abc_TwoExactPermAddFanin( pFans, i, Abc_Random(0) % Limit ) )
                        break;
                if ( Try == 100 )
                    fOk = 0;
            }
            if ( pFans[2*i] > pFans[2*i+1] )
                ABC_SWAP( int, pFans[2*i], pFans[2*i+1] );
        }
        if ( fOk && Abc_TwoExactPermCheck(pFans, nVars, nNodes, 0) && Abc_TwoExactPermAddDcs(pFans, nVars, nNodes, nDcs, 2*nSeeds, 1) )
        {
            ABC_FREE( pUsed );
            return pFans;
        }
        ABC_FREE( pUsed );
        ABC_FREE( pFans );
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Computes a cofactor and writes its hexadecimal truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Abc_TwoExactCofactorHex( char * pHex, int nVars, int iVar, int Value )
{
    word pTruth[64], pCof[64];
    int nCofVars = nVars - 1;
    int nMints = 1 << nCofVars;
    char * pRes = ABC_ALLOC( char, (nCofVars >= 2 ? (1 << (nCofVars-2)) : 1) + 10 );
    int m;
    memset( pTruth, 0, sizeof(word) * 64 );
    memset( pCof,   0, sizeof(word) * 64 );
    Abc_TtReadHex( pTruth, pHex );
    for ( m = 0; m < nMints; m++ )
    {
        int Low = m & ((1 << iVar) - 1);
        int High = m >> iVar;
        int Mint = Low | (Value << iVar) | (High << (iVar + 1));
        if ( Abc_TtGetBit(pTruth, Mint) )
            Abc_TtSetBit( pCof, m );
    }
    Extra_PrintHexadecimalString( pRes, (unsigned *)pCof, nCofVars );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Runs two-input-gate exact synthesis.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactRun( Bmc_EsPar_t * pPars )
{
    extern int  Exa_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern int  Exa_ManExactSynthesis2( Bmc_EsPar_t * pPars );
    return pPars->fGlucose ? Exa_ManExactSynthesis( pPars ) : Exa_ManExactSynthesis2( pPars );
}

/**Function*************************************************************

  Synopsis    [Searches for a minimum-size exact implementation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_TwoExactRunMin( Bmc_EsPar_t * pPars, int nNodeMax )
{
    int n, nNodeBeg = pPars->nVars + 1;
    int fFound = 0;
    for ( n = nNodeBeg; n <= nNodeMax; n++ )
    {
        if ( !pPars->fSilent )
            printf( "\nTrying N = %d:\n", n );
        pPars->nNodes = n;
        ABC_FREE( pPars->pSolFans );
        fFound = Abc_TwoExactRun( pPars );
        if ( fFound )
            return n;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Derives topology seeds from cofactor implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Abc_TwoExactCofactorSeeds( Bmc_EsPar_t * pPars, int nNodeMax )
{
    int Counts[16][16];
    int v, c, i, k, nPairs = 0;
    Vec_Int_t * vPairs = Vec_IntAlloc( 16 );
    memset( Counts, 0, sizeof(Counts) );
    if ( pPars->nVars > 16 )
        return vPairs;
    for ( v = 0; v < pPars->nVars; v++ )
    for ( c = 0; c < 2; c++ )
    {
        Bmc_EsPar_t CofPars, * pCof = &CofPars;
        char * pCofHex = Abc_TwoExactCofactorHex( pPars->pTtStr, pPars->nVars, v, c );
        int nFound;
        Bmc_EsParSetDefault( pCof );
        pCof->nVars      = pPars->nVars - 1;
        pCof->nNodes     = nNodeMax;
        pCof->pTtStr     = pCofHex;
        pCof->fOnlyAnd   = pPars->fOnlyAnd;
        pCof->fGlucose   = pPars->fGlucose;
        pCof->RuntimeLim = pPars->RuntimeLim ? pPars->RuntimeLim : 1;
        pCof->fSilent    = 1;
        nFound = Abc_TwoExactRunMin( pCof, nNodeMax );
        if ( nFound )
        {
            printf( "Cofactor %c=%d: minimum N = %d, truth = %s\n", 'a' + v, c, nFound, pCofHex );
            for ( i = 0; i < nFound; i++ )
            {
                int Fan0 = pCof->pSolFans[2*i];
                int Fan1 = pCof->pSolFans[2*i+1];
                if ( Fan0 >= pCof->nVars || Fan1 >= pCof->nVars )
                    continue;
                Fan0 += Fan0 >= v;
                Fan1 += Fan1 >= v;
                if ( Fan0 > Fan1 )
                    ABC_SWAP( int, Fan0, Fan1 );
                Counts[Fan0][Fan1]++;
            }
        }
        else
            printf( "Cofactor %c=%d: no solution up to N = %d, truth = %s\n", 'a' + v, c, nNodeMax, pCofHex );
        ABC_FREE( pCof->pSolFans );
        ABC_FREE( pCofHex );
    }
    for ( k = pPars->nVars * pPars->nVars; k > 0; k-- )
    {
        int BestI = -1, BestJ = -1, Best = 0;
        for ( i = 0; i < pPars->nVars; i++ )
        for ( v = i + 1; v < pPars->nVars; v++ )
            if ( Counts[i][v] > Best )
            {
                Best = Counts[i][v];
                BestI = i;
                BestJ = v;
            }
        if ( Best == 0 )
            break;
        printf( "Frequent seed %d: %c%c appears %d time%s.\n", ++nPairs, 'a' + BestI, 'a' + BestJ, Best, Best == 1 ? "" : "s" );
        for ( v = 0; v < Best; v++ )
            Vec_IntPush( vPairs, BestI * pPars->nVars + BestJ );
        Counts[BestI][BestJ] = 0;
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Handles two-input-gate exact synthesis.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTwoExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int  Exa_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern int  Exa_ManExactSynthesis2( Bmc_EsPar_t * pPars );
    extern void Exa_ManExactSynthesis4( Bmc_EsPar_t * pPars );
    extern void Exa_ManExactSynthesis5( Bmc_EsPar_t * pPars );
    extern void Exa_ManExactSynthesis6( Bmc_EsPar_t * pPars, char * pFileName );
    extern void Exa_ManExactSynthesis7( Bmc_EsPar_t * pPars, int GateSize );
    int c, fKissat = 0, fKissat2 = 0, fUseNands = 0, GateSize = 0, nCandPerms = 0, nPermDcs = 0, fTryMin = 0, fSmartGen = 0, nSeedNodes = 0;
    Bmc_EsPar_t Pars, * pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "INTGSPCDEabdconugklmtxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVars < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodes < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->RuntimeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->RuntimeLim < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            GateSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( GateSize < 0 )
                goto usage;
            break;            
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a file name.\n" );
                goto usage;
            }
            pPars->pGuide = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a variable permutation.\n" );
                goto usage;
            }
            pPars->pPermStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCandPerms = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCandPerms < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nPermDcs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPermDcs < 0 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeedNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeedNodes < 0 )
                goto usage;
            break;
        case 'a':
            pPars->fOnlyAnd ^= 1;
            break;
        case 'b':
            fUseNands ^= 1;
            break;            
        case 'd':
            pPars->fDynConstr ^= 1;
            break;
        case 'c':
            pPars->fDumpCnf ^= 1;
            break;
        case 'o':
            pPars->fFewerVars ^= 1;
            break;
        case 'n':
            pPars->fOrderNodes ^= 1;
            break;
        case 'u':
            pPars->fUniqFans ^= 1;
            break;
        case 'g':
            pPars->fGlucose ^= 1;
            break;
        case 'k':
            fKissat ^= 1;
            break;
        case 'l':
            fKissat2 ^= 1;
            break;
        case 'm':
            pPars->fCard ^= 1;
            break;
        case 't':
            fTryMin ^= 1;
            break;
        case 'x':
            fSmartGen ^= 1;
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
    if ( argc == globalUtilOptind + 1 )
    {
        if ( strstr(argv[globalUtilOptind], ".") )
        {
            if ( pPars->pPermStr || nCandPerms )
            {
                Abc_Print( -1, "Permutation options -P and -C are not supported when reading the function from a file.\n" );
                return 1;
            }
            Exa_ManExactSynthesis6( pPars, argv[globalUtilOptind] );
            return 0;
        }
        pPars->pTtStr = argv[globalUtilOptind];
    }
    if ( pPars->pTtStr == NULL )
    {
        Abc_Print( -1, "Truth table should be given on the command line.\n" );
        return 1;
    }
    if ( pPars->nVars >= 2 && (1 << (pPars->nVars-2)) != (int)strlen(pPars->pTtStr) )
    {
        Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", (1 << (pPars->nVars-2)), strlen(pPars->pTtStr) );
        return 1;
    }
    if ( pPars->nVars > pPars->nNodes * (2 - 1) + 1 )
    {
        Abc_Print( -1, "Function with %d variales cannot be implemented with %d two-input gates.\n", pPars->nVars, pPars->nNodes );
        return 1;
    }
    if ( pPars->nVars > 10 )
    {
        Abc_Print( -1, "Function should not have more than 10 inputs.\n" );
        return 1;
    }
    if ( nPermDcs && nCandPerms == 0 )
    {
        Abc_Print( -1, "Command line switch \"-D\" can only be used together with \"-C\".\n" );
        return 1;
    }
    if ( fSmartGen && nCandPerms == 0 )
    {
        Abc_Print( -1, "Command line switch \"-x\" can only be used together with \"-C\".\n" );
        return 1;
    }
    if ( nSeedNodes && !fSmartGen )
    {
        Abc_Print( -1, "Command line switch \"-E\" can only be used together with \"-x\".\n" );
        return 1;
    }
    if ( nCandPerms && pPars->pPermStr )
    {
        Abc_Print( -1, "Command line switch \"-C\" cannot be used together with \"-P\".\n" );
        return 1;
    }
    if ( fTryMin && nCandPerms )
    {
        Abc_Print( -1, "Command line switch \"-t\" cannot be used together with \"-C\".\n" );
        return 1;
    }
    if ( nPermDcs > 2 * pPars->nNodes )
    {
        Abc_Print( -1, "The number of don't-care positions should not exceed %d.\n", 2 * pPars->nNodes );
        return 1;
    }
    if ( pPars->pPermStr )
    {
        char * pToken = pPars->pPermStr;
        int nEntries = 0;
        while ( *pToken )
        {
            int iObj = -1;
            if ( *pToken == '_' )
            {
                pToken++;
                continue;
            }
            if ( !Abc_TwoExactPermParseObj(&pToken, pPars->nVars, pPars->nNodes, &iObj) )
            {
                Abc_Print( -1, "Permutation should use '*', '_', input variables 'a' through '%c', or internal nodes 'A' through '%c'.\n", 'a' + pPars->nVars - 1, 'A' + Abc_MinInt(pPars->nNodes, 26) - 1 );
                return 1;
            }
            nEntries++;
        }
        if ( nEntries != 2 * pPars->nNodes )
        {
            Abc_Print( -1, "Permutation should contain %d non-separator symbols (instead of %d).\n", 2 * pPars->nNodes, nEntries );
            return 1;
        }
        if ( fUseNands || fKissat || fKissat2 || pPars->fCard )
        {
            Abc_Print( -1, "Permutation option -P is currently supported by the default and Glucose (-g) twoexact engines.\n" );
            return 1;
        }
    }
    if ( nCandPerms )
    {
        int i, fFound = 0, nGenerated = 0, nFailed = 0, fSilentSave = pPars->fSilent;
        Vec_Int_t * vSeedPairs = NULL;
        abctime clk = Abc_Clock();
        if ( fUseNands || fKissat || fKissat2 || pPars->fCard )
        {
            Abc_Print( -1, "Candidate generation with -C is currently supported by the default and Glucose (-g) twoexact engines.\n" );
            return 1;
        }
        Abc_Random( 1 );
        if ( fSmartGen )
        {
            printf( "Deriving frequent seed nodes from cofactors.\n" );
            vSeedPairs = Abc_TwoExactCofactorSeeds( pPars, pPars->nNodes );
            nSeedNodes = Abc_MinInt( nSeedNodes, Vec_IntSize(vSeedPairs) );
            printf( "Trying %d smart candidate input assignments with %d frozen seed node%s and %d randomized don't-care position%s.\n", nCandPerms, nSeedNodes, nSeedNodes == 1 ? "" : "s", nPermDcs, nPermDcs == 1 ? "" : "s" );
        }
        else
            printf( "Trying %d random candidate input assignments with %d randomized don't-care position%s.\n", nCandPerms, nPermDcs, nPermDcs == 1 ? "" : "s" );
        pPars->fSilent = 1;
        for ( i = 0; i < nCandPerms; i++ )
        {
            int * pFans = fSmartGen ? Abc_TwoExactPermRandomSeeded( pPars->nVars, pPars->nNodes, nPermDcs, vSeedPairs, nSeedNodes ) : Abc_TwoExactPermRandom( pPars->nVars, pPars->nNodes, nPermDcs );
            char * pPerm, * pStruct;
            if ( pFans == NULL )
            {
                nFailed++;
                continue;
            }
            pPerm = Abc_TwoExactPermEncode( pFans, pPars->nVars, pPars->nNodes );
            pStruct = Abc_TwoExactPermEncodeFull( pFans, pPars->nVars, pPars->nNodes );
            nGenerated++;
            pPars->pPermFans = pFans;
            pPars->pPermStr = pPerm;
            if ( nGenerated == 1 || nGenerated % 10000 == 0 )
                printf( "Trying candidate %d/%d: %s\n", nGenerated, nCandPerms, pStruct );
            fFound = pPars->fGlucose ? Exa_ManExactSynthesis( pPars ) : Exa_ManExactSynthesis2( pPars );
            if ( fFound )
            {
                pPars->fSilent = fSilentSave;
                Abc_TwoExactRun( pPars );
                printf( "Found solution using candidate %d: %s\n", nGenerated, pStruct );
                ABC_FREE( pStruct );
                ABC_FREE( pPerm );
                ABC_FREE( pFans );
                break;
            }
            ABC_FREE( pStruct );
            ABC_FREE( pPerm );
            ABC_FREE( pFans );
            pPars->pPermStr = NULL;
            pPars->pPermFans = NULL;
        }
        pPars->pPermStr = NULL;
        pPars->pPermFans = NULL;
        pPars->fSilent = fSilentSave;
        Vec_IntFreeP( &vSeedPairs );
        ABC_FREE( pPars->pSolFans );
        if ( !fFound )
            printf( "No solution found after trying %d generated candidate%s (%d generation failure%s).\n", nGenerated, nGenerated == 1 ? "" : "s", nFailed, nFailed == 1 ? "" : "s" );
        Abc_PrintTime( 1, "Total candidate-search runtime", Abc_Clock() - clk );
        return 0;
    }
    if ( fTryMin )
    {
        if ( fUseNands || fKissat || fKissat2 || pPars->fCard )
        {
            Abc_Print( -1, "Minimum-node enumeration with -t is currently supported by the default and Glucose (-g) twoexact engines.\n" );
            return 1;
        }
        if ( pPars->nNodes < pPars->nVars + 1 )
        {
            Abc_Print( -1, "Command line switch \"-t\" expects \"-N <num>\" to be at least %d.\n", pPars->nVars + 1 );
            return 1;
        }
        if ( !Abc_TwoExactRunMin(pPars, pPars->nNodes) )
            printf( "No solution found from N = %d through N = %d.\n", pPars->nVars + 1, pPars->nNodes );
        ABC_FREE( pPars->pSolFans );
        return 0;
    }
    if ( fUseNands )
        Exa_ManExactSynthesis7( pPars, GateSize );
    else if ( fKissat || pPars->fCard )
        Exa_ManExactSynthesis4( pPars );
    else if ( fKissat2 )
        Exa_ManExactSynthesis5( pPars );
    else if ( pPars->fGlucose )
        Exa_ManExactSynthesis( pPars );
    else
        Exa_ManExactSynthesis2( pPars );
    ABC_FREE( pPars->pSolFans );
    return 0;

usage:
    Abc_Print( -2, "usage: twoexact [-INTGCDE <num>] [-S str] [-P str] [-abdconugklmtxvh] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of multi-input function using two-input gates\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", pPars->nVars );
    Abc_Print( -2, "\t-N <num> : the number of two-input nodes [default = %d]\n", pPars->nNodes );
    Abc_Print( -2, "\t-T <num> : the runtime limit in seconds [default = %d]\n", pPars->RuntimeLim );
    Abc_Print( -2, "\t-G <num> : the largest allowed gate size (NANDs only) [default = %d]\n", GateSize );
    Abc_Print( -2, "\t-S <str> : structural guidance from the user [default = %s]\n", pPars->pGuide ? pPars->pGuide : "unknown" );    
    Abc_Print( -2, "\t-P <str> : fixed input permutation; '_' separates gates, '*' leaves fanin free [default = %s]\n", pPars->pPermStr ? pPars->pPermStr : "none" );
    Abc_Print( -2, "\t-C <num> : number of random candidate permutations to try [default = %d]\n", nCandPerms );
    Abc_Print( -2, "\t-D <num> : number of fixed variable positions randomized to '*' in each candidate [default = %d]\n", nPermDcs );
    Abc_Print( -2, "\t-E <num> : number of frequent cofactor seed nodes used with -x [default = %d]\n", nSeedNodes );
    Abc_Print( -2, "\t-a       : toggle using only AND-gates (without XOR-gates) [default = %s]\n", pPars->fOnlyAnd ? "yes" : "no" );
    Abc_Print( -2, "\t-b       : toggle using only NAND-gates [default = %s]\n", fUseNands ? "yes" : "no" );
    Abc_Print( -2, "\t-d       : toggle using dynamic constraint addition [default = %s]\n", pPars->fDynConstr ? "yes" : "no" );
    Abc_Print( -2, "\t-c       : toggle dumping CNF into a file [default = %s]\n", pPars->fDumpCnf ? "yes" : "no" );
    Abc_Print( -2, "\t-o       : toggle using additional optimizations [default = %s]\n", pPars->fFewerVars ? "yes" : "no" );
    Abc_Print( -2, "\t-n       : toggle ordering internal nodes [default = %s]\n", pPars->fOrderNodes ? "yes" : "no" );
    Abc_Print( -2, "\t-u       : toggle using unique fanouts [default = %s]\n", pPars->fUniqFans ? "yes" : "no" );
    Abc_Print( -2, "\t-g       : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", pPars->fGlucose ? "yes" : "no" );
    Abc_Print( -2, "\t-k       : toggle using Kissat by Armin Biere [default = %s]\n", fKissat ? "yes" : "no" );
    Abc_Print( -2, "\t-l       : toggle using Kissat by Armin Biere [default = %s]\n", fKissat2 ? "yes" : "no" );
    Abc_Print( -2, "\t-m       : toggle using CaDiCaL by Armin Biere [default = %s]\n", pPars->fCard ? "yes" : "no" );
    Abc_Print( -2, "\t-t       : toggle trying increasing node counts up to \"-N <num>\" [default = %s]\n", fTryMin ? "yes" : "no" );
    Abc_Print( -2, "\t-x       : toggle smart candidate generation using cofactor seed nodes [default = %s]\n", fSmartGen ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<hex>    : truth table in hex notation\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           For example, command line \"twoexact -g -I 5 -N 12 169AE443\"\n" );
    Abc_Print( -2, "\t           synthesizes the smallest circuit composed of two-input gates\n" );
    Abc_Print( -2, "\t           for the only NPN class of 5-input functions that requires 12 gates;\n" );
    Abc_Print( -2, "\t           all other functions can be realized with 11 two-input gates or less\n" );
    Abc_Print( -2, "\t           (see Section 7.1.2 \"Boolean evaluation\" in the book The Art of Computer Programming by Donald Knuth)\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int  Exa7_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern int  Exa8_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern int  Exa8_ManExactSynthesisIter( Bmc_EsPar_t * pPars );
    extern int  Exa3_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern void Exa3_ManExactSynthesis2( Bmc_EsPar_t * pPars );
    extern void Exa3_ManExactSynthesisRand( Bmc_EsPar_t * pPars );
    extern char * Abc_NtkReadTruth( Abc_Ntk_t * pNtk );
    int c;
    Bmc_EsPar_t Pars, * pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMKTFUSYPiaorfgckdsmpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVars < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodes < 0 )
                goto usage;
            break;
       case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->RuntimeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->RuntimeLim < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRandFuncs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'U':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-U\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMintNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Seed < 0 )
                goto usage;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->pSymStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->pPermStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'i':
            pPars->fUseIncr ^= 1;
            break;
        case 'a':
            pPars->fOnlyAnd ^= 1;
            break;
        case 'o':
            pPars->fFewerVars ^= 1;
            break;
        case 'r':
            pPars->fLutCascade ^= 1;
            break;
        case 'f':
            pPars->fLutInFixed ^= 1;
            break;
        case 'g':
            pPars->fGlucose ^= 1;
            break;
        case 'c':
            pPars->fCadical ^= 1;
            break;
        case 'k':
            pPars->fKissat ^= 1;
            break;
        case 'd':
            pPars->fDumpBlif ^= 1;
            break;
        case 's':
            pPars->fSilent ^= 1;
            break;
        case 'm':
            pPars->fMinNodes ^= 1;
            break;
        case 'p':
            pPars->fUsePerm ^= 1;
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
    if ( pPars->pPermStr && (pPars->nLutSize * pPars->nNodes != (int)strlen(pPars->pPermStr)) )
    {
        Abc_Print( -1, "Permutation \"%s\" has %d symbols instead of expected %d = %d * %d symbols (LutSize * nLuts).\n", 
            pPars->pPermStr, (int)strlen(pPars->pPermStr), pPars->nLutSize * pPars->nNodes, pPars->nLutSize, pPars->nNodes );
        return 1;
    }
    if ( pPars->pPermStr && !pPars->fLutCascade )
        Abc_Print( 0, "If LUT mapping is not enabled (switch \"-r\"), permutation has not effect.\n" );
    if ( argc == globalUtilOptind + 1 )
        pPars->pTtStr = argv[globalUtilOptind];
    else if ( argc == globalUtilOptind && Abc_FrameReadNtk(pAbc) )
    {
        Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
        if ( Abc_NtkCiNum(pNtk) > 30 )
        {
            Abc_Print( -1, "Cannot derive truth table from network: too many inputs (%d > 30).\n", Abc_NtkCiNum(pNtk) );
            Abc_Print( -1, "Please provide truth table on the command line or use a smaller network.\n" );
            return 1;
        }
        if ( Abc_NtkCoNum(pNtk) != 1 )
        {
            Abc_Print( -1, "Cannot derive truth table from network: network must have exactly one output (has %d).\n", Abc_NtkCoNum(pNtk) );
            return 1;
        }
        pPars->pTtStr = Abc_NtkReadTruth( pNtk );
        if ( pPars->pTtStr )
        {
            pPars->nVars = Abc_NtkCiNum(pNtk);
            Abc_Print( 0, "Derived %d-input truth table from current network.\n", pPars->nVars );
        }
        else
        {
            Abc_Print( -1, "Failed to derive truth table from current network.\n" );
            return 1;
        }
    }
    if ( pPars->pTtStr == NULL && pPars->pSymStr == NULL && pPars->nRandFuncs == 0 )
    {
        Abc_Print( -1, "Truth table should be given on the command line, or derived from current single-output network.\n" );
        return 1;
    }
    if ( pPars->nVars == 0 && pPars->pTtStr )
        pPars->nVars = 2 + Abc_Base2Log((int)strlen(pPars->pTtStr));
    if ( pPars->pTtStr && (1 << (pPars->nVars-2)) != (int)strlen(pPars->pTtStr) )
    {
        Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", (1 << (pPars->nVars-2)), strlen(pPars->pTtStr) );
        return 1;
    }
    if ( pPars->nVars == 0 && pPars->pSymStr )
        pPars->nVars = (int)strlen(pPars->pSymStr) - 1;
    if ( pPars->pSymStr && pPars->nVars+1 != strlen(pPars->pSymStr) )
    {
        Abc_Print( -1, "The char string of the %d-variable symmetric function should have %d zeros and ones (instead of %d).\n", pPars->nVars, pPars->nVars+1, strlen(pPars->pSymStr) );
        return 1;
    }
    if ( pPars->nVars > pPars->nNodes * (pPars->nLutSize - 1) + 1 )
    {
        Abc_Print( -1, "Function with %d variales cannot be implemented with %d %d-input LUTs.\n", pPars->nVars, pPars->nNodes, pPars->nLutSize );
        return 1;
    }
    if ( pPars->fKissat || pPars->fCadical )
    {
        if ( pPars->nVars > 14 )
        {
            Abc_Print( -1, "Function should not have more than 14 inputs.\n" );
            return 1;
        }
        if ( pPars->nLutSize > 8 )
        {
            Abc_Print( -1, "Node size should not be more than 8 inputs.\n" );
            return 1;
        }
    }
    else
    {
        if ( pPars->nVars > 12 )
        {
            Abc_Print( -1, "Function should not have more than 12 inputs.\n" );
            return 1;
        }
        if ( pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "Node size should not be more than 6 inputs.\n" );
            return 1;
        }
    }
    if ( pPars->nRandFuncs ) {
        pPars->fGlucose = 1;
        Exa3_ManExactSynthesisRand( pPars );
    }
    else if ( pPars->fGlucose )
        Exa3_ManExactSynthesis( pPars );
    else if ( pPars->fCadical )
        Exa7_ManExactSynthesis( pPars );
    else if ( pPars->fKissat )
        Exa8_ManExactSynthesis( pPars );
    else
        Exa3_ManExactSynthesis2( pPars );
    if ( argc == globalUtilOptind && Abc_FrameReadNtk(pAbc) )
        ABC_FREE( pPars->pTtStr );
    return 0;

usage:
    Abc_Print( -2, "usage: lutexact [-NMKTFUS <num>] [-Y string] [-P string] [-iaorfgckdsmpvh] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of N-input function using M K-input lookup-tables\n" );
    Abc_Print( -2, "\t-N <num> : the number of input variables [default = %d]\n", pPars->nVars );
    Abc_Print( -2, "\t-M <num> : the number of K-input nodes [default = %d]\n", pPars->nNodes );
    Abc_Print( -2, "\t-K <num> : the number of node fanins [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-T <num> : the runtime limit in seconds [default = %d]\n", pPars->RuntimeLim );
    Abc_Print( -2, "\t-F <num> : the number of random functions to try [default = unused]\n" );
    Abc_Print( -2, "\t-U <num> : the number of positive minterms in the random function [default = unused]\n" );
    Abc_Print( -2, "\t-S <num> : the random seed for random function generation with -F <num> [default = %d]\n", pPars->Seed );
    Abc_Print( -2, "\t-Y <str> : charasteristic string of a symmetric function [default = %s]\n", pPars->pSymStr ? pPars->pSymStr : "unused" );
    Abc_Print( -2, "\t-P <str> : variable permutation (for example, \"abcd_aef\" for S44) [default = %s]\n", pPars->pPermStr ? pPars->pPermStr : "unused" );
    Abc_Print( -2, "\t-i       : toggle using incremental solving [default = %s]\n", pPars->fUseIncr ? "yes" : "no" );
    Abc_Print( -2, "\t-a       : toggle using only AND-gates when K = 2 [default = %s]\n", pPars->fOnlyAnd ? "yes" : "no" );
    Abc_Print( -2, "\t-o       : toggle using additional optimizations [default = %s]\n", pPars->fFewerVars ? "yes" : "no" );
    Abc_Print( -2, "\t-r       : toggle synthesizing a single-rail cascade [default = %s]\n", pPars->fLutCascade ? "yes" : "no" );
    Abc_Print( -2, "\t-f       : toggle fixing LUT inputs in cascade mapping [default = %s]\n", pPars->fLutInFixed ? "yes" : "no" );
    Abc_Print( -2, "\t-g       : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", pPars->fGlucose ? "yes" : "no" );
    Abc_Print( -2, "\t-c       : toggle using CaDiCal 2.2.0-rc1 by Armin Biere et al [default = %s]\n", pPars->fCadical ? "yes" : "no" );
    Abc_Print( -2, "\t-k       : toggle using Kissat 4.0.2 by Armin Biere [default = %s]\n", pPars->fKissat ? "yes" : "no" );
    Abc_Print( -2, "\t-d       : toggle dumping decomposed networks into BLIF files [default = %s]\n", pPars->fDumpBlif ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggle silent computation (no messages, except when a solution is found) [default = %s]\n", pPars->fSilent ? "yes" : "no" );
    Abc_Print( -2, "\t-m       : toggle minimum-node solution possibly smaller than \"-M <num>\" [default = %s]\n", pPars->fMinNodes ? "yes" : "no" );
    Abc_Print( -2, "\t-p       : toggle use specialized permutation when minimizing nodes [default = %s]\n", pPars->fUsePerm ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<hex>    : truth table in hex notation\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAndExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Exa9_ManExactSynthesis( Bmc_EsPar_t * pPars );
    extern int Exa9_ManExactSynthesisIter( Bmc_EsPar_t * pPars );
    extern char * Abc_NtkReadTruth( Abc_Ntk_t * pNtk );
    int c;
    Bmc_EsPar_t Pars, * pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMTSHYiadsmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVars < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodes < 0 )
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->RuntimeLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->RuntimeLim < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Seed < 0 )
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->n1HotAlgo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'Y':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Y\" should be followed by a string.\n" );
                goto usage;
            }
            pPars->pSymStr = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'i':
            pPars->fUseIncr ^= 1;
            break;
        case 'a':
            pPars->fOnlyAnd ^= 1;
            break;
        case 'd':
            pPars->fDumpBlif ^= 1;
            break;
        case 's':
            pPars->fSilent ^= 1;
            break;
        case 'm':
            pPars->fMinNodes ^= 1;
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
    if ( argc == globalUtilOptind + 1 )
        pPars->pTtStr = argv[globalUtilOptind];
    else if ( argc == globalUtilOptind && Abc_FrameReadNtk(pAbc) ) 
    {
        pPars->pTtStr = Abc_NtkReadTruth( Abc_FrameReadNtk(pAbc) );
        if ( pPars->pTtStr )  
            pPars->nVars = Abc_NtkCiNum(Abc_FrameReadNtk(pAbc));
    }
    if ( pPars->pTtStr == NULL && pPars->pSymStr == NULL && pPars->nRandFuncs == 0 )
    {
        Abc_Print( -1, "Truth table should be given on the command line.\n" );
        return 1;
    }
    if ( pPars->nVars == 0 && pPars->pTtStr )
        pPars->nVars = 2 + Abc_Base2Log((int)strlen(pPars->pTtStr));
    if ( pPars->pTtStr && (1 << (pPars->nVars-2)) != (int)strlen(pPars->pTtStr) )
    {
        Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", (1 << (pPars->nVars-2)), strlen(pPars->pTtStr) );
        return 1;
    }
    if ( pPars->nVars == 0 && pPars->pSymStr )
        pPars->nVars = (int)strlen(pPars->pSymStr) - 1;
    if ( pPars->pSymStr && pPars->nVars+1 != strlen(pPars->pSymStr) )
    {
        Abc_Print( -1, "The char string of the %d-variable symmetric function should have %d zeros and ones (instead of %d).\n", pPars->nVars, pPars->nVars+1, strlen(pPars->pSymStr) );
        return 1;
    }
    if ( pPars->nVars > pPars->nNodes + 1 )
    {
        Abc_Print( -1, "Function with %d variales cannot be implemented with %d two-input nodes.\n", pPars->nVars, pPars->nNodes );
        return 1;
    }
    if ( pPars->nVars > 14 )
    {
        Abc_Print( -1, "Function should not have more than 14 inputs.\n" );
        return 1;
    }
    if ( pPars->nNodes > 16 )
    {
        Abc_Print( -1, "Node count cannot be more than 16 inputs.\n" );
        return 1;
    }
    if ( pPars->fMinNodes )
        Exa9_ManExactSynthesisIter( pPars );
    else
        Exa9_ManExactSynthesis( pPars );
    if ( argc == globalUtilOptind && Abc_FrameReadNtk(pAbc) )
        ABC_FREE( pPars->pTtStr );
    return 0;

usage:
    Abc_Print( -2, "usage: andexact [-NMTSH <num>] [-Y str] [-iadmsvh] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of N-input function using two-input gates\n" );
    Abc_Print( -2, "\t-N <num> : the number of input variables [default = %d]\n", pPars->nVars );
    Abc_Print( -2, "\t-M <num> : the number of two-input nodes [default = %d]\n", pPars->nNodes );
    Abc_Print( -2, "\t-T <num> : the runtime limit in seconds [default = %d]\n", pPars->RuntimeLim );
    Abc_Print( -2, "\t-S <num> : the random seed for random function generation with -F <num> [default = %d]\n", pPars->Seed );
    Abc_Print( -2, "\t-H <num> : the 1-hotness algorithm used (0 = naive; 1 = seq; 2 = bim; 3 = cmd) [default = %d]\n", pPars->n1HotAlgo );
    Abc_Print( -2, "\t-Y <str> : charasteristic string of a symmetric function [default = %s]\n", pPars->pSymStr ? pPars->pSymStr : "unused" );
    Abc_Print( -2, "\t-i       : toggle using incremental SAT (CEGAR over minterms) [default = %s]\n", pPars->fUseIncr ? "yes" : "no" );
    Abc_Print( -2, "\t-a       : toggle using only AND-gates when K = 2 [default = %s]\n", pPars->fOnlyAnd ? "yes" : "no" );
    Abc_Print( -2, "\t-m       : toggle minimum-node solution possibly smaller than \"-M <num>\" [default = %s]\n", pPars->fMinNodes ? "yes" : "no" );
    Abc_Print( -2, "\t-d       : toggle dumping decomposed networks into BLIF files [default = %s]\n", pPars->fDumpBlif ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggle silent computation (no messages, except when a solution is found) [default = %s]\n", pPars->fSilent ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<hex>    : truth table in hex notation\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAllExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Zyx_ManExactSynthesis( Bmc_EsPar_t * pPars );
    int c;
    Bmc_EsPar_t Pars, * pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MINKianegvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMajSupp = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMajSupp < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVars < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodes < 0 )
                goto usage;
            break;
       case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 0 )
                goto usage;
            break;
        case 'i':
            pPars->fUseIncr ^= 1;
            break;
        case 'a':
            pPars->fOnlyAnd ^= 1;
            break;
        case 'n':
            pPars->fOrderNodes ^= 1;
            break;
        case 'e':
            pPars->fEnumSols ^= 1;
            break;
        case 'g':
            pPars->fGlucose ^= 1;
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
    if ( pPars->nMajSupp > 0 )
    {
        if ( pPars->nMajSupp != 5 && pPars->nMajSupp != 7 && pPars->nMajSupp != 9 )
        {
            Abc_Print( -1, "Currently only support majority with 5, 7 or 9 inputs.\n" );
            return 1;
        }
        pPars->nVars = pPars->nMajSupp;
        pPars->nLutSize = 3;
        pPars->fMajority = 1;
        pPars->fUseIncr = 1;
        if ( pPars->nNodes == 0 )
        {
            if ( pPars->nMajSupp == 5 )
                pPars->nNodes = 4;
            if ( pPars->nMajSupp == 7 )
                pPars->nNodes = 7;
            if ( pPars->nMajSupp == 9 )
                pPars->nNodes = 10;
        }
    }
    else
    {
        if ( pPars->nVars == 0 )
        {
            Abc_Print( -1, "The number of variables (-I num) needs to be specified on the command line.\n" );
            return 1;
        }
        if ( pPars->nNodes == 0 )
        {
            Abc_Print( -1, "The number of nodes (-N num) needs to be specified on the command line.\n" );
            return 1;
        }
        if ( argc == globalUtilOptind + 1 )
            pPars->pTtStr = argv[globalUtilOptind];
        if ( pPars->pTtStr == NULL )
        {
            Abc_Print( -1, "Truth table should be given on the command line.\n" );
            return 1;
        }
        if ( (1 << (pPars->nVars-2)) != (int)strlen(pPars->pTtStr) )
        {
            Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", (1 << (pPars->nVars-2)), strlen(pPars->pTtStr) );
            return 1;
        }
    }
    if ( pPars->nVars > pPars->nNodes * (pPars->nLutSize - 1) + 1 )
    {
        Abc_Print( -1, "Function with %d variales cannot be implemented with %d %d-input LUTs.\n", pPars->nVars, pPars->nNodes, pPars->nLutSize );
        return 1;
    }
    if ( pPars->nVars > 10 )
    {
        Abc_Print( -1, "Function should not have more than 10 inputs.\n" );
        return 1;
    }
    if ( pPars->nLutSize > 6 )
    {
        Abc_Print( -1, "Node size should not be more than 6 inputs.\n" );
        return 1;
    }
    if ( !pPars->fUseIncr )
    {
        if ( pPars->fMajority )
        {
            Abc_Print( -1, "Cannot synthesize majority in the non-incremental mode (use \'-i\').\n" );
            return 1;
        }
        if ( pPars->nLutSize > 3 )
        {
            Abc_Print( -1, "Cannot synthesize LUT4 and larger in non-incremental mode (use \'-i\').\n" );
            return 1;
        }
    }
    Zyx_ManExactSynthesis( pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: allexact [-MIKN <num>] [-ianevh] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of I-input function using N K-input gates\n" );
    Abc_Print( -2, "\t-M <num> : the majority support size (overrides -I and -K) [default = %d]\n", pPars->nMajSupp );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", pPars->nVars );
    Abc_Print( -2, "\t-K <num> : the number of node fanins [default = %d]\n", pPars->nLutSize );
    Abc_Print( -2, "\t-N <num> : the number of K-input nodes [default = %d]\n", pPars->nNodes );
    Abc_Print( -2, "\t-i       : toggle using incremental solving [default = %s]\n", pPars->fUseIncr ? "yes" : "no" );
    Abc_Print( -2, "\t-a       : toggle using only AND-gates when K = 2 [default = %s]\n", pPars->fOnlyAnd ? "yes" : "no" );
    Abc_Print( -2, "\t-n       : toggle using node ordering by fanins [default = %s]\n", pPars->fOrderNodes ? "yes" : "no" );
    Abc_Print( -2, "\t-e       : toggle enumerating all solutions [default = %s]\n", pPars->fEnumSols ? "yes" : "no" );
//    Abc_Print( -2, "\t-g       : toggle using Glucose 3.0 by Gilles Audemard and Laurent Simon [default = %s]\n", pPars->fGlucose ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<hex>    : truth table in hex notation\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTopoExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkTopoExact( Abc_Ntk_t * pFunc, Abc_Ntk_t * pTopo, int nTimeOut, int nSeed, int fAndGates, int fVerbose );
    Abc_Ntk_t * pNtkRes = NULL;
    Abc_Ntk_t * pTopo = NULL;
    int nTimeOut = 0;    
    int nSeed = 0;
    char * pFileName = NULL;
    int c, fAndGates = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TSavh" ) ) != EOF )
    {
        switch ( c )
        {
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
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeed < 0 )
                goto usage;
            break;
       case 'a':
            fAndGates ^= 1;
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
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pAbc->pNtkCur) )
    {
        Abc_Print( -1, "This command expect an AIG as the current network and BLIF file on the command line.\n" );
        return 1;
    }
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    if ( pFileName == NULL )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    pTopo = Io_Read( pFileName, Io_ReadFileType(pFileName), 1, 0 );
    if ( pTopo == NULL ) 
    {
        Abc_Print( -1, "The topology file is not specified on the command line.\n" );
        return 1;
    }
    if ( Abc_NtkGetFaninMax(pTopo) > 6 )
    {
        Abc_NtkDelete( pTopo );
        Abc_Print( -1, "The topology network has nodes with more than 6 inputs.\n" );
        return 1;
    }
    if ( Abc_NtkCiNum(pAbc->pNtkCur) != Abc_NtkCiNum(pTopo) )
    {
        Abc_NtkDelete( pTopo );
        Abc_Print( -1, "The number of combinational inputs of the networks does not match.\n" );
        return 1;
    }
    if ( Abc_NtkCoNum(pAbc->pNtkCur) != Abc_NtkCoNum(pTopo) )
    {
        Abc_NtkDelete( pTopo );
        Abc_Print( -1, "The number of combinational outputs of the networks does not match.\n" );
        return 1;
    }
    pTopo = Abc_NtkDupDfs( pNtkRes = pTopo );
    Abc_NtkDelete( pNtkRes );
    pNtkRes = Abc_NtkTopoExact( pAbc->pNtkCur, pTopo, nTimeOut, nSeed, fAndGates, fVerbose );
    Abc_NtkDelete( pTopo );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );    
    return 0;

usage:
    Abc_Print( -2, "usage: topoexact [-TS num] [-avh] <file>\n" );
    Abc_Print( -2, "\t           exact synthesis solution for the fixed topology\n" );
    Abc_Print( -2, "\t-T <num> : the runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-S <num> : the random seed to randomize the SAT solver [default = %d]\n", nSeed );
    Abc_Print( -2, "\t-a       : toggle using only and-gates (not xor-gates) [default = %s]\n", fAndGates ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<file>   : BLIF file name with the topology\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNetExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Tn_ReadHexTruth( char * pInput, word * pTruth );
    extern void Tn_SolveProblem( int nIns, int nOuts, word * pOuts, char * pTypes, int nEdgeLimit, int nLevelLimit, int nSolsMax, int Seed, int TimeOut, int fVerbose );
    int c, nIns = 0, nOuts = 0, nEdgeLimit = 0, nLevelLimit = 0, nSolsMax = 1, Seed = 0, TimeOut = 0, fVerbose = 0;
    char * pTypes = NULL;  
    word Truths[16] = {0};    
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CELNSTVvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pTypes = argv[globalUtilOptind];
            globalUtilOptind++;
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
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nEdgeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nEdgeLimit < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelLimit < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSolsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSolsMax < 0 )
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
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            fVerbose = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fVerbose < 0 )
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

    for ( c = globalUtilOptind; c < argc; c++ ) {
        if ( Abc_TtIsHexDigit(argv[c][0]) == -1 ) {
            Abc_Print( -1, "Cannot read truth table \"%s\".\n", argv[c] );
            goto usage;
        }
        int nVarsOut = Tn_ReadHexTruth( argv[c], Truths + nOuts++ );
        if ( nIns == 0 )
            nIns = nVarsOut;
        else if ( nIns != nVarsOut ) {
            Abc_Print( -1, "The support size of output functions is not the same.\n" ); 
            goto usage;
        }
    }

    printf( "Finished reading %d output%s\n\n", nOuts, nOuts == 1 ? "" : "s" );
    Tn_SolveProblem( nIns, nOuts, Truths, pTypes, nEdgeLimit, nLevelLimit, nSolsMax, Seed, TimeOut, fVerbose );    
    return 0;

usage:

    Abc_Print( -2, "usage: netexact -C <str> [-ELNSTV <num>] <truth[0]> ... <truth[m-1]>\n" );
    Abc_Print( -2, "                   this program synthesizes networks for multi-output functions\n" );
    Abc_Print( -2, "\n" );     
    Abc_Print( -2, "      -C <str>  :  the configuration string (no default)\n" );
    Abc_Print( -2, "      -E <num>  :  the max number of edges (default = no limit)\n" );
    Abc_Print( -2, "      -L <num>  :  the max number of levels (default = no limit)\n" );        
    Abc_Print( -2, "      -N <num>  :  the max number of solutions (default = 1)\n" );        
    Abc_Print( -2, "      -S <num>  :  the random seed (default = 0)\n" );        
    Abc_Print( -2, "      -T <num>  :  the timeout in seconds (default = no timeout)\n" );                
    Abc_Print( -2, "      -V <num>  :  the verbosiness levels (default = %d)\n", fVerbose );             
    Abc_Print( -2, "    <truth[0]>  :  the truth table of the first output in the hexadecimal notation\n" );
    Abc_Print( -2, "  <truth[m-1]>  :  the truth table of the last output in the hexadecimal notation\n" );
    Abc_Print( -2, "                   the truth tables are assumed to depend on the same variables\n" );
    Abc_Print( -2, "                   the strings should contain 2^(<num_inputs>-2) hexadecimal digits\n" );
    Abc_Print( -2, "\n" );        
    Abc_Print( -2, "                   Example 1: Synthesizing 3-node 2-edge 2-input and-gate:\n" );
    Abc_Print( -2, "                     %s -C *11** -E 2  8\n", argv[0] );
    Abc_Print( -2, "                   Example 2: Synthesizing 4-node 5-edge 3-input majority gate:\n" );
    Abc_Print( -2, "                     %s -C *111*** -E 5  E8\n", argv[0] );        
    Abc_Print( -2, "                   Example 3: Synthesizing 10-edge 3-input 2-output full-adder:\n" );
    Abc_Print( -2, "                     %s -C *222****** -E 10  E8 96\n", argv[0] );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Zyx_TestExact( char * pFileName );
    char * pFileName = NULL;
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
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    if ( pFileName == NULL )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }
    Zyx_TestExact( pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: testexact <file>\n" );
    Abc_Print( -2, "\t           tests solution of the exact synthesis problem\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t<file>   : file name in the specified format\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMajGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gem_Enumerate( int nVars, int fDump, int fVerbose );
    int c, nVars = 8, fDump = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ndvh" ) ) != EOF )
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
    Gem_Enumerate( nVars, fDump, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: majgen [-N <num>] [-dvh]>\n" );
    Abc_Print( -2, "\t           generates networks for majority gates\n" );
    Abc_Print( -2, "\t-N <num> : the maximum number of variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-d       : toggle dumping functions into a file [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Exmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Mio_IntallSimpleLibrary2();
    extern Gia_Man_t * Gia_ManKSatMapping( word Truth, int nIns, int nNodes, int nBound, int Seed, int fMultiLevel, int nBTLimit, int nTimeout, int fVerbose, int fKeepFile, int argc, char ** argv, char * pGuide );
    Gia_Man_t * pTemp = NULL; char * pTruth = NULL, * pGuide = NULL; word Truth = 0;
    int c, nVars = 0, nNodes = 0, nVars2, Seed = 0, nBTLimit = 0, nBound = 0, fMultiLevel = 0, nTimeout = 0, fKeepFile = 0, fVerbose = 0; 
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NBRCTSmfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodes < 0 )
            {
                Abc_Print( -1, "Bound on a solution should be a positive integer.\n" );
                goto usage;
            }
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nBound = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBound < 0 )
            {
                Abc_Print( -1, "Bound on a solution should be a positive integer.\n" );
                goto usage;
            }
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            Seed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 )
            {
                Abc_Print( -1, "Conflict limit should be a positive integer.\n" );
                goto usage;
            }
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;            
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a file name.\n" );
                goto usage;
            }
            pGuide = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'm':
            fMultiLevel ^= 1;
            break;
        case 'f':
            fKeepFile ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Truth table should be given on the command line.\n" );
        return 1;
    }
    pTruth = argv[globalUtilOptind];
    nVars = Abc_Base2Log(4*strlen(pTruth));
    if ( (1 << nVars) != 4*strlen(pTruth) ) 
    {
        Abc_Print( -1, "The string (%s) does not look like a hex truth table.\n", pTruth );
        return 1;
    }
    if ( nVars > 6 ) 
    {
        Abc_Print( -1, "Currently only works for functions of 6 of fewer inputs.\n" );
        return 1;
    }
    if ( nNodes == 0 )
    {
        Abc_Print( -1, "The number of nodes should be given on the command line (-N <num>).\n" );
        return 1;
    }
    nVars2 = Abc_TtReadHex( &Truth, pTruth );
    assert( nVars2 == nVars );
    pTemp = Gia_ManKSatMapping( Truth, nVars, nNodes, nBound, Seed, fMultiLevel, nBTLimit, nTimeout, fVerbose, fKeepFile, argc, argv, pGuide );
    if ( pTemp )  {
        //Mio_IntallSimpleLibrary2();
        Abc_FrameUpdateGia( pAbc, pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &exmap [-NBRCT num] [-S str] [-mfvh] <truth>\n" );
    Abc_Print( -2, "\t           performs simple mapping of the truth table\n" );
    Abc_Print( -2, "\t-N num   : the number of nodes [default = %d]\n", nNodes );
    Abc_Print( -2, "\t-B num   : the bound on the solution size [default = %d]\n", nBound );
    Abc_Print( -2, "\t-R num   : random number generator seed [default = %d]\n", Seed );
    Abc_Print( -2, "\t-C num   : the conflict limit [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-T num   : runtime limit in seconds [default = %d]\n", nTimeout );    
    Abc_Print( -2, "\t-S str   : structural guidance from the user [default = %s]\n", pGuide ? pGuide : "unknown" );  
    Abc_Print( -2, "\t-m       : toggles using multi-level primitives [default = %s]\n", fMultiLevel? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggles keeping the intermediate CNF file [default = %s]\n", fKeepFile? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
