/* Placement-aware command copies. Ordinary ABC commands remain upstream. */
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "opt/rwr/rwr.h"
#include "ext-pa/paPlace.h"
#include "ext-pa/paRewrite.h"
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
ABC_NAMESPACE_IMPL_START
/* Unlike atoi, reject malformed/overflowing user input before ABC allocates
 * cut and simulation workspaces from it. */
static int Pa_ReadNonnegativeInt( int argc, char ** argv, int * pValue )
{
    char * End;
    long Value;
    if ( globalUtilOptind >= argc ) return 0;
    errno = 0;
    Value = strtol(argv[globalUtilOptind++], &End, 10);
    if ( errno || End == argv[globalUtilOptind - 1] || *End
      || Value < 0 || Value > INT_MAX ) return 0;
    *pValue = (int)Value;
    return 1;
}

extern int Pa_NtkRewrite( Abc_Ntk_t *, int, int, int, int, int );
extern int Pa_NtkRefactorPhysical( Abc_Ntk_t *, int, int, int, int, int, int, int );
extern Abc_Ntk_t * Pa_NtkStrash( Abc_Ntk_t *, int, int, int );
int Pa_CommandStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pObj;
    int c;
    int fAllNodes;
    int fRecord;
    int fCleanup;
    int fComplOuts;
    int fTransferMappedPlacement;
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

    // Capture mapped-cell centers before Pa_NtkStrash changes gate pData to
    // local Hop AIGs.  Each new AIG node is seeded during cell strashing.
    fTransferMappedPlacement = pNtk && Abc_NtkHasMapping(pNtk)
        && Pa_ManHasPlacement(pNtk);
    if ( fTransferMappedPlacement && !Pa_ManBeginMappedUnmap(pNtk) )
    {
        Abc_Print( -1, "pa_strash: failed to capture mapped placement.\n" );
        return 1;
    }
    // get the new network
    pNtkRes = Pa_NtkStrash( pNtk, fAllNodes, fCleanup, fRecord );
    if ( pNtkRes == NULL )
    {
        Pa_ManAbortMappedUnmap();
        Abc_Print( -1, "Strashing has failed.\n" );
        return 1;
    }
    if ( fTransferMappedPlacement && !Pa_ManFinishMappedUnmap(pNtkRes) )
    {
        Pa_ManAbortMappedUnmap();
        Abc_NtkDelete(pNtkRes);
        Abc_Print( -1, "pa_strash: could not assign coordinates to every AIG node.\n" );
        return 1;
    }
    if ( fComplOuts )
    Abc_NtkForEachPo( pNtkRes, pObj, c )
        Abc_ObjXorFaninC( pObj, 0 );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: pa_strash [-acrih]\n" );
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

int Pa_CommandRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int ScoreMode = 0;
    double TimingWeight = 0.50;
    int fTimingWeightSet = 0;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    int fClusterEvaluation;
    int fTimingEvaluation;
    int TimingEffort = 2, fTimingEffortSet = 0;
    // set defaults
    fUpdateLevel = 1;
    fUseZeros    = 0;
    fVerbose     = 0;
    fVeryVerbose = 0;
    fClusterEvaluation = 0;
    fTimingEvaluation = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvwhctTWSE" ) ) != EOF )
    {
        switch ( c )
        {
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

        case 'c':
            fClusterEvaluation ^= 1;
            break;
        case 'E':
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * End;
                long Value = strtol(argv[globalUtilOptind++], &End, 10);
                if ( End == argv[globalUtilOptind - 1] || *End != '\0'
                  || Value < 0 || Value > 2 ) goto usage;
                TimingEffort = (int)Value;
                fTimingEffortSet = 1;
            }
            break;
        case 't':
            fTimingEvaluation = 1;
            break;
        case 'T':
            fTimingEvaluation = 2;
            break;
        case 'S':
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                long Value = strtol(argv[globalUtilOptind++], &pEnd, 10);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0'
                  || Value < 0 || Value > 2 ) goto usage;
                ScoreMode = (int)Value;
            }
            break;
        case 'W':
            fTimingWeightSet = 1;
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                TimingWeight = strtod(argv[globalUtilOptind++], &pEnd);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0' || TimingWeight != TimingWeight
                  || TimingWeight < 0.0 || TimingWeight > 10.0 ) goto usage;
            }
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( fTimingEffortSet && fTimingEvaluation != 1 )
    {
        Abc_Print(-1, "-E requires -t.\n");
        return 1;
    }
    if ( ScoreMode == 2 && fTimingEvaluation != 1 )
    {
        Abc_Print(-1, "-S 2 requires -t.\n");
        return 1;
    }
    if ( fTimingWeightSet && !fTimingEvaluation )
    {
        Abc_Print(-1, "-W requires -t or -T.\n");
        return 1;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }
    if ( fClusterEvaluation && !Pa_ManHasInheritedPlacement(pNtk) )
    {
        Abc_Print( -1, "pa_rw -c requires a placed mapped netlist followed by pa_strash.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    Pa_ManSetClusterEvaluation( fClusterEvaluation );
    Pa_ManSetTimingEffort(fTimingEvaluation ? TimingEffort : 0);
    Pa_ManSetScoreMode(ScoreMode);
    Pa_ManSetTimingWeight(TimingWeight);
    Pa_ManSetTimingEvaluation( fTimingEvaluation );
    RetValue = Pa_NtkRewrite( pNtk, fUpdateLevel, fUseZeros, fVerbose, fVeryVerbose, 1 );
    Pa_ManSetTimingEvaluation( 0 );
    Pa_ManSetTimingWeight(0.50);
    Pa_ManSetScoreMode(0);
    Pa_ManSetExactTiming(0);
    Pa_ManSetClusterEvaluation( 0 );
    if ( RetValue <= 0 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
        Pa_ManClearPlacement();
        return 1;
    }
    else
    {
        Abc_NtkDelete( pDup );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: pa_rw [-lzvwhctT] [-WSE <num>]\n" );
    Abc_Print(-2, "\t-S <num> : experimental score: 0 original, 1 node-priority, 2 integrated criticality\n");
    Abc_Print( -2, "\t-W <num> : timing-score weight with -t or -T [default = 0.5]\n" );
    Abc_Print( -2, "\t         performs technology-independent rewriting of the AIG\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printout subgraph statistics [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t        requires pa_place on the current AIG\n" );
    Abc_Print( -2, "\t-c     : snap new AIG nodes to inherited mapped-cell clusters\n" );
    Abc_Print( -2, "\t-E <num> : with -t: 0 bounded, 1 lazy required, 2 full incremental [default = 2]\n" );
    Abc_Print( -2, "\t-t     : use the local root-slack timing score\n" );
    Abc_Print( -2, "\t-T     : use the experimental full-cone timing score\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pa_CommandRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int ScoreMode = 0;
    double TimingWeight = 0.50;
    int fTimingWeightSet = 0;
    int fBalanced = 0;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, RetValue;
    int nNodeSizeMax;
    int nMinSaved;
    int nConeSizeMax;
    int fUpdateLevel;
    int fUseZeros;
    int fUseDcs;
    int fVerbose;
    int fClusterEvaluation;
    int fTimingEvaluation;
    int TimingEffort = 2, fTimingEffortSet = 0;
    extern int Pa_NtkRefactorPhysical( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nMinSaved, int nConeSizeMax, int fUpdateLevel, int fUseZeros, int fUseDcs, int fVerbose );

    // set defaults
    nNodeSizeMax = 10;
    // Physical refactor has always allowed zero-gain, positive-score edits.
    // Preserve that default while honoring an explicit -M constraint.
    nMinSaved    =  0;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    fClusterEvaluation = 0;
    fTimingEvaluation = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NMCdlzvhctTWaSE" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nNodeSizeMax) )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nMinSaved) )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nConeSizeMax) )
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

        case 'c':
            fClusterEvaluation ^= 1;
            break;
        case 'E':
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * End;
                long Value = strtol(argv[globalUtilOptind++], &End, 10);
                if ( End == argv[globalUtilOptind - 1] || *End != '\0'
                  || Value < 0 || Value > 2 ) goto usage;
                TimingEffort = (int)Value;
                fTimingEffortSet = 1;
            }
            break;
        case 't':
            fTimingEvaluation = 1;
            break;
        case 'T':
            fTimingEvaluation = 2;
            break;
        case 'a': fBalanced ^= 1; break;
        case 'S':
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                long Value = strtol(argv[globalUtilOptind++], &pEnd, 10);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0'
                  || Value < 0 || Value > 2 ) goto usage;
                ScoreMode = (int)Value;
            }
            break;
        case 'W':
            fTimingWeightSet = 1;
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                TimingWeight = strtod(argv[globalUtilOptind++], &pEnd);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0' || TimingWeight != TimingWeight
                  || TimingWeight < 0.0 || TimingWeight > 10.0 ) goto usage;
            }
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fUseZeros )
        nMinSaved = 0;
    if ( nMinSaved == 0 )
        fUseZeros = 1;

    if ( fTimingEffortSet && fTimingEvaluation != 1 )
    {
        Abc_Print(-1, "-E requires -t.\n");
        return 1;
    }
    if ( ScoreMode == 2 && fTimingEvaluation != 1 )
    {
        Abc_Print(-1, "-S 2 requires -t.\n");
        return 1;
    }
    if ( fTimingWeightSet && !fTimingEvaluation )
    {
        Abc_Print(-1, "-W requires -t or -T.\n");
        return 1;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }
    if ( fClusterEvaluation && !Pa_ManHasInheritedPlacement(pNtk) )
    {
        Abc_Print( -1, "pa_rf -c requires a placed mapped netlist followed by pa_strash.\n" );
        return 1;
    }
    if ( nNodeSizeMax > 15 )
    {
        Abc_Print( -1, "The cone size cannot exceed 15.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        Abc_Print( -1, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup( pNtk );
    Pa_ManSetClusterEvaluation( fClusterEvaluation );
    Pa_ManSetBalancedRefactor(fBalanced);
    Pa_ManSetTimingEffort(fTimingEvaluation ? TimingEffort : 0);
    Pa_ManSetScoreMode(ScoreMode);
    Pa_ManSetTimingWeight(TimingWeight);
    Pa_ManSetTimingEvaluation( fTimingEvaluation );
    RetValue = Pa_NtkRefactorPhysical( pNtk, nNodeSizeMax, nMinSaved,
        nConeSizeMax, fUpdateLevel, fUseZeros, fUseDcs, fVerbose );
    Pa_ManSetTimingEvaluation( 0 );
    Pa_ManSetTimingWeight(0.50);
    Pa_ManSetScoreMode(0);
    Pa_ManSetExactTiming(0);
    Pa_ManSetBalancedRefactor(0);
    Pa_ManSetClusterEvaluation( 0 );
    if ( RetValue <= 0 )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        printf( "An error occurred during computation. The original network is restored.\n" );
        Pa_ManClearPlacement();
        return 1;
    }
    else
    {
        Abc_NtkDelete( pDup );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: pa_rf [-NMCWSE <num>] [-dlzvhctTa]\n" );
    Abc_Print(-2, "\t-a       : also evaluate an arrival-balanced factored form\n");
    Abc_Print(-2, "\t-S <num> : experimental score: 0 original, 1 node-priority, 2 integrated criticality\n");
    Abc_Print( -2, "\t-W <num> : timing-score weight with -t or -T [default = 0.5]\n" );
    Abc_Print( -2, "\t           performs technology-independent refactoring of the AIG\n" );
    Abc_Print( -2, "\t-N <num> : the max support of the collapsed node [default = %d]\n", nNodeSizeMax );
    Abc_Print( -2, "\t-M <num> : the min number of nodes saved after one step (0 <= num) [default = %d]\n", nMinSaved );
    Abc_Print( -2, "\t-C <num> : the max support of the containing cone [default = %d]\n", nConeSizeMax );
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : allow zero-gain replacements (overrides -M)\n" );
    Abc_Print( -2, "\t-d       : toggle using don't-cares [default = %s]\n", fUseDcs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t          requires pa_place on the current AIG\n" );
    Abc_Print( -2, "\t-c       : snap new AIG nodes to inherited mapped-cell clusters\n" );
    Abc_Print( -2, "\t-E <num> : with -t: 0 bounded, 1 lazy required, 2 full incremental [default = 2]\n" );
    Abc_Print( -2, "\t-t       : use the local root-slack timing score\n" );
    Abc_Print( -2, "\t-T       : use the experimental full-cone timing score\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pa_CommandResubstitute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int RS_CUT_MIN =  4;
    int RS_CUT_MAX = 16;
    int c;
    int ScoreMode = 0;
    double TimingWeight = 0.50;
    int fTimingWeightSet = 0;
    int nCutsMax;
    int nNodesMax;
    int nLevelsOdc;
    int nMinSaved;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    int fTiming = 0, fClusterEvaluation = 0, fMinSavedSet = 0, RetValue;
    Abc_Ntk_t * pDup = NULL;

    // set defaults
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;
    nMinSaved    =  1;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fVerbose     =  0;
    fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNMFlzvwhctTWS" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nCutsMax) )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nNodesMax) )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            fMinSavedSet = 1;
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nMinSaved) )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            if ( !Pa_ReadNonnegativeInt(argc, argv, &nLevelsOdc) )
                goto usage;
            break;

        case 'c': fClusterEvaluation ^= 1; break;
        case 't': fTiming = 1; break;
        case 'T': fTiming = 2; break;
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
        case 'S':
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                long Value = strtol(argv[globalUtilOptind++], &pEnd, 10);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0'
                  || Value < 0 || Value > 2 ) goto usage;
                ScoreMode = (int)Value;
            }
            break;
        case 'W':
            fTimingWeightSet = 1;
            if ( globalUtilOptind >= argc ) goto usage;
            {
                char * pEnd;
                TimingWeight = strtod(argv[globalUtilOptind++], &pEnd);
                if ( pEnd == argv[globalUtilOptind - 1] || *pEnd != '\0' || TimingWeight != TimingWeight
                  || TimingWeight < 0.0 || TimingWeight > 10.0 ) goto usage;
            }
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !fMinSavedSet )
        nMinSaved = 0;
    if ( fUseZeros )
        nMinSaved = 0;
    if ( nMinSaved == 0 )
        fUseZeros = 1;

    if ( ScoreMode == 2 && fTiming != 1 )
    {
        Abc_Print(-1, "-S 2 requires -t.\n");
        return 1;
    }
    if ( fTimingWeightSet && !fTiming )
    {
        Abc_Print(-1, "-W requires -t or -T.\n");
        return 1;
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < RS_CUT_MIN || nCutsMax > RS_CUT_MAX )
    {
        Abc_Print( -1, "Can only compute cuts for %d <= K <= %d.\n", RS_CUT_MIN, RS_CUT_MAX );
        return 1;
    }
    if ( nNodesMax < 0 || nNodesMax > 3 )
    {
        Abc_Print( -1, "Can only resubstitute at most 3 nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    if ( fClusterEvaluation && !Pa_ManHasInheritedPlacement(pNtk) )
    {
        Abc_Print( -1, "pa_rs -c requires a placed mapped netlist followed by pa_strash.\n" );
        return 1;
    }

    // modify the current network
    pDup = Abc_NtkDup(pNtk);
    Pa_ManSetClusterEvaluation(fClusterEvaluation);
    Pa_ManSetScoreMode(ScoreMode);
    Pa_ManSetTimingWeight(TimingWeight);
    Pa_ManSetTimingEvaluation(fTiming);
    RetValue = Pa_NtkResubstitute(pNtk, nCutsMax, nNodesMax, nMinSaved,
        nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose);
    Pa_ManSetTimingEvaluation(0);
    Pa_ManSetTimingWeight(0.50);
    Pa_ManSetScoreMode(0);
    Pa_ManSetClusterEvaluation(0);
    if ( RetValue <= 0 )
    {
        Pa_ManClearPlacement();
        Abc_FrameReplaceCurrentNetwork(pAbc, pDup);
        Abc_Print( -1, "Physical resubstitution failed; original network restored.\n" );
        return 1;
    }
    Abc_NtkDelete(pDup);
    return 0;

usage:
    Abc_Print( -2, "usage: pa_rs [-KNMFWS <num>] [-clztTvwh]\n" );
    Abc_Print(-2, "\t-S <num> : experimental score: 0 original, 1 node-priority, 2 integrated criticality\n");
    Abc_Print( -2, "\t-W <num> : timing-score weight with -t or -T [default = 0.5]\n" );
    Abc_Print( -2, "\t           performs technology-independent restructuring of the AIG\n" );
    Abc_Print( -2, "\t-K <num> : the max cut size (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );
    Abc_Print( -2, "\t-N <num> : the max number of nodes to add (0 <= num <= 3) [default = %d]\n", nNodesMax );
    Abc_Print( -2, "\t-M <num> : the min number of nodes saved after one step (0 <= num) [default = %d]\n", nMinSaved );
    Abc_Print( -2, "\t-F <num> : the number of fanout levels for ODC computation [default = %d]\n", nLevelsOdc );
    Abc_Print( -2, "\t          ranks candidates by nodes and HPWL (default -M 0)\n" );
    Abc_Print( -2, "\t-c       : use inherited mapped-cell clusters after pa_strash\n" );
    Abc_Print( -2, "\t-t       : include local placement-based timing in the PA score\n" );
    Abc_Print( -2, "\t-T       : include full-cone timing (slower ablation)\n" );
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle verbose printout of ODC computation [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

void Pa_RegisterSynthesisCommands( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd(pAbc, "Physical synthesis", "pa_rw", Pa_CommandRewrite, 1);
    Cmd_CommandAdd(pAbc, "Physical synthesis", "pa_rf", Pa_CommandRefactor, 1);
    Cmd_CommandAdd(pAbc, "Physical synthesis", "pa_rs", Pa_CommandResubstitute, 1);
    Cmd_CommandAdd(pAbc, "Physical synthesis", "pa_strash", Pa_CommandStrash, 1);
}
ABC_NAMESPACE_IMPL_END
