/**CFile****************************************************************

  FileName    [emap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Multi-output gate mapper.]

  Synopsis    [ABC command entry points.]

***********************************************************************/

#include "emap.h"

#include "base/abc/abc.h"
#include "base/cmd/cmd.h"
#include "base/main/mainInt.h"
#include "map/mio/mio.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Emap_CommandCountMogPairs( Mio_Library_t * pLib );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the package.]

***********************************************************************/
void Emap_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "SC mapping", "emap", Emap_Command, 1 );
}

/**Function*************************************************************

  Synopsis    [Stops the package.]

***********************************************************************/
void Emap_End( Abc_Frame_t * pAbc )
{
    (void)pAbc;
}

/**Function*************************************************************

  Synopsis    [Counts physical two-output gates represented as twin gates.]

***********************************************************************/
static int Emap_CommandCountMogPairs( Mio_Library_t * pLib )
{
    Mio_Gate_t * pGate;
    int nTwinOutputs = 0;
    if ( pLib == NULL )
        return 0;
    Mio_LibraryForEachGate( pLib, pGate )
        nTwinOutputs += (Mio_GateReadTwin(pGate) != NULL);
    return nTwinOutputs / 2;
}

/**Function*************************************************************

  Synopsis    [Runs the ABC-native exact mapper.]

***********************************************************************/
int Emap_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Abc_Ntk_t * pNtkRes;
    Emap_Par_t Pars, * pPars = &Pars;
    int c;

    memset( pPars, 0, sizeof(Emap_Par_t) );
    pPars->nCutNum     = 16;
    pPars->nFlowRounds = 2;
    pPars->nAreaRounds = 4;
    pPars->fUseMogs    = 1;
    pPars->fNldm       = 1;
    pPars->nPropBudget = 2000;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CFADBamNOvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutNum < 1 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFlowRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlowRounds < 0 )
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nAreaRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaRounds < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating-point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget < 0 )
                goto usage;
            break;
        case 'a':
            pPars->fAreaMode ^= 1;
            break;
        case 'm':
            pPars->fUseMogs ^= 1;
            break;
        case 'N':
            pPars->fNldm ^= 1;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPropBudget = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPropBudget < 0 )
                goto usage;
            break;
        case 'O':
            pPars->fLegacy ^= 1;
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
    if ( argc != globalUtilOptind )
        goto usage;

    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "There is no current network.\n" );
        return 1;
    }
    if ( pLib == NULL )
    {
        fprintf( pAbc->Err, "There is no current GENLIB library. Use read_genlib/read_lib first.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pAbc->Err, "The current network is not an AIG. Run strash first.\n" );
        return 1;
    }
    //Rejects sequential networks
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( pAbc->Err, "The current network has latches; emap maps combinational networks only.\n" );
        return 1;
    }

    if ( pPars->fVerbose )
    {
        int nMogPairs = pPars->fUseMogs ? Emap_CommandCountMogPairs( pLib ) : 0;
        fprintf( pAbc->Out, "ABC-native emap setup: PI = %d  PO = %d  AND = %d\n",
            Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk), Abc_NtkNodeNum(pNtk) );
        fprintf( pAbc->Out, "GENLIB \"%s\": gates = %d  MOG pairs = %d  MOG use = %s  mode = %s%s\n",
            Mio_LibraryReadName(pLib), Mio_LibraryReadGateNum(pLib), nMogPairs, pPars->fUseMogs ? "yes" : "no",
            pPars->fAreaMode ? "area" : "delay", pPars->fLegacy ? "  (original implementation)" : "" );
    }

    if ( pPars->fLegacy )
        pNtkRes = Emap_ManMapAigStructural( pNtk, pLib, pPars->fUseMogs, pPars->fAreaMode, pPars->fVerbose );
    else
        pNtkRes = Emap_ManMapNew( pNtk, pLib, pPars );
    if ( pNtkRes == NULL )
    {
        fprintf( pAbc->Err, "ABC-native emap structural mapping has failed.\n" );
        return 1;
    }

    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: emap [-CFAB num] [-D float] [-amNOvh]\n" );
    fprintf( pAbc->Err, "\t         maps the current AIG using the current GENLIB library; if the library\n" );
    fprintf( pAbc->Err, "\t         was read by \"read_lib\", the cells are timed with its NLDM tables\n" );
    fprintf( pAbc->Err, "\t-C num : the maximum number of priority cuts per node [default = %d]\n", pPars->nCutNum );
    fprintf( pAbc->Err, "\t-F num : the number of area-flow rounds [default = %d]\n", pPars->nFlowRounds );
    fprintf( pAbc->Err, "\t-A num : the maximum number of exact-area rounds [default = %d]\n", pPars->nAreaRounds );
    fprintf( pAbc->Err, "\t-B num : the incremental timing budget in node updates per AIG node and round;\n" );
    fprintf( pAbc->Err, "\t         after that, each round is timed and repaired as a whole (0 = no limit) [default = %d]\n", pPars->nPropBudget );
    fprintf( pAbc->Err, "\t-D float : the delay target (0 = the best delay) [default = %.2f]\n", pPars->DelayTarget );
    fprintf( pAbc->Err, "\t-a     : toggle area-oriented mode without required-time pruning [default = %s]\n", pPars->fAreaMode ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-m     : toggle using multi-output gates when present [default = %s]\n", pPars->fUseMogs ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-N     : toggle NLDM timing when a Liberty library is loaded (else GENLIB delays) [default = %s]\n", pPars->fNldm ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-O     : toggle running the original implementation (ignores -CFABDN) [default = %s]\n", pPars->fLegacy ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n\n" );
    fprintf( pAbc->Err, "\tThe mapper is inspired by \"emap\" in Mockturtle developed by Alessandro Tempia Calvino\n" );
    fprintf( pAbc->Err, "\tavailable at https://mockturtle.readthedocs.io/en/latest/algorithms/mapper.html\n" );
    fprintf( pAbc->Err, "\tand described in A. T. Calvino and G. De Micheli, \"Technology mapping using multi-output\n" );
    fprintf( pAbc->Err, "\tlibrary cells\", Proc. ICCAD\'23, https://aletempiac.github.io/publication/2023_006\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
