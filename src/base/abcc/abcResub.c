/**CFile****************************************************************

  FileName    [abcResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Resubstitution and window optimization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "opt/mfs/mfs.h"
#include "opt/sfm/sfm.h"
#include "opt/res/res.h"
#include "opt/sbd/sbd.h"
#include "opt/eslim/eSLIM.h"
#include "opt/eslim2/eSLIM2.h"
#include "aig/gia/giaEdit.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

//static int Abc_CommandImfs                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMfs                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMfs2                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubstitute           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubUnate             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubCore              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubCheck             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SimRsb             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resub              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resub2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Mfs                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Mfsd               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9eSLIM              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9eSLIM2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9elSLIM             ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );

/**Function*************************************************************

  Synopsis    [Registers resubstitution and window optimization commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitResub( Abc_Frame_t * pAbc )
{
//    Cmd_CommandAdd( pAbc, "Synthesis",    "imfs",          Abc_CommandImfs,             1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mfs",           Abc_CommandMfs,              1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mfs2",          Abc_CommandMfs2,             1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub",         Abc_CommandResubstitute,     1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub_unate",   Abc_CommandResubUnate,       1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub_core",    Abc_CommandResubCore,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub_check",   Abc_CommandResubCheck,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&simrsb",       Abc_CommandAbc9SimRsb,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resub",        Abc_CommandAbc9Resub,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resub2",       Abc_CommandAbc9Resub2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mfs",          Abc_CommandAbc9Mfs,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&mfs2",         Abc_CommandAbc9Mfsd,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&eslim",        Abc_CommandAbc9eSLIM,                  0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&eslim2",       Abc_CommandAbc9eSLIM2,                 0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "elslim",        Abc_CommandAbc9elSLIM,                 0 );
}

////////////////////////////////////////////////////////////////////////
///                       FUNCTION DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////

#if 0
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandImfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Res_Par_t Pars, * pPars = &Pars;
    int c;

    // set defaults
    pPars->nWindow      = 62;
    pPars->nCands       =  5;
    pPars->nSimWords    =  4;
    pPars->nGrowthLevel =  0;
    pPars->fArea        =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WSCLavwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSimWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSimWords < 1 || pPars->nSimWords > 256 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCands < 0 || pPars->nCands > ABC_INFINITY )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY )
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkResynthesize( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: imfs [-W <NM>] [-LCS <num>] [-avwh]\n" );
    Abc_Print( -2, "\t           performs resubstitution-based resynthesis with interpolation\n" );
    Abc_Print( -2, "\t           (there is another command for resynthesis after LUT mapping, \"lutpack\")\n" );
    Abc_Print( -2, "\t-W <NM>  : fanin/fanout levels (NxM) of the window (00 <= NM <= 99) [default = %d%d]\n", pPars->nWindow/10, pPars->nWindow%10 );
    Abc_Print( -2, "\t-C <num> : the max number of resub candidates (1 <= n) [default = %d]\n", pPars->nCands );
    Abc_Print( -2, "\t-S <num> : the number of simulation words (1 <= n <= 256) [default = %d]\n", pPars->nSimWords );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-a       : toggle optimization for area only [default = %s]\n", pPars->fArea? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printout subgraph statistics [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}
#endif

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Mfs_Par_t Pars, * pPars = &Pars;
    int c;
    // set defaults
    Abc_NtkMfsParsDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFDMLCdraestpgcvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinTfoLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinTfoLevs < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFanoutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFanoutsMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinMax < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY )
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
        case 'd':
            pPars->fRrOnly ^= 1;
            break;
        case 'r':
            pPars->fResub ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'e':
            pPars->fMoreEffort ^= 1;
            break;
        case 's':
            pPars->fSwapEdge ^= 1;
            break;
        case 't':
            pPars->fOneHotness ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'g':
            pPars->fGiaSat ^= 1;
            break;
        case 'c':
            pPars->fPrintCares ^= 1;
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkMfs( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: mfs [-WFDMLC <num>] [-draestpgcvh]\n" );
    Abc_Print( -2, "\t           performs don't-care-based optimization of logic networks\n" );
    Abc_Print( -2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n", pPars->nWinTfoLevs );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n", pPars->nFanoutsMax );
    Abc_Print( -2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n", pPars->nDepthMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n", pPars->nWinMax );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-d       : toggle performing redundancy removal [default = %s]\n", pPars->fRrOnly? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggle resubstitution and dc-minimization [default = %s]\n", pPars->fResub? "resub": "dc-min" );
    Abc_Print( -2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n", pPars->fArea? "area": "area+edges" );
    Abc_Print( -2, "\t-e       : toggle high-effort resubstitution [default = %s]\n", pPars->fMoreEffort? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle evaluation of edge swapping [default = %s]\n", pPars->fSwapEdge? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggle using artificial one-hotness conditions [default = %s]\n", pPars->fOneHotness? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggle power-aware optimization [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggle using new SAT solver [default = %s]\n", pPars->fGiaSat? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle printing careset at each node [default = %s]\n", pPars->fPrintCares? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMfs2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkPerformMfs( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars );
    extern int Abc_NtkMfsAfterICheck( Abc_Ntk_t * p, int nFrames, int nFramesAdd, Vec_Int_t * vFlops, Sfm_Par_t * pPars );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Sfm_Par_t Pars, * pPars = &Pars;
    int c, fIndDCs = 0, fUseAllFfs = 0, nFramesAdd = 0;
    // set defaults
    Sfm_ParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFDMLCZNIdaeijlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfoLevMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfoLevMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFanoutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFanoutMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinSizeMax < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < -ABC_INFINITY || pPars->nGrowthLevel > ABC_INFINITY )
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
        case 'Z':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFirstFixed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFirstFixed < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodesMax < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesAdd < 0 )
                goto usage;
            break;
        case 'd':
            pPars->fRrOnly ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'e':
            pPars->fMoreEffort ^= 1;
            break;
        case 'i':
            fIndDCs ^= 1;
            break;
        case 'j':
            fUseAllFfs ^= 1;
            break;
        case 'l':
            pPars->fUseDcs ^= 1;
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
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }
    if ( fIndDCs )
    {
        if ( fUseAllFfs )
        {
            pAbc->nIndFrames = 1;
            Vec_IntFreeP( &pAbc->vIndFlops );
            pAbc->vIndFlops = Vec_IntAlloc( Abc_NtkLatchNum(pNtk) );
            Vec_IntFill( pAbc->vIndFlops, Abc_NtkLatchNum(pNtk), 1 );
        }
        if ( pAbc->nIndFrames <= 0 )
        {
            Abc_Print( -1, "The number of k-inductive frames is not specified.\n" );
            return 0;
        }
        if ( pAbc->vIndFlops == NULL )
        {
            Abc_Print( -1, "The set of k-inductive flops is not specified.\n" );
            return 0;
        }
        if ( Vec_IntSize(pAbc->vIndFlops) != Abc_NtkLatchNum(pNtk) )
        {
            Abc_Print( -1, "The saved flop count (%d) does not match that of the current network (%d).\n",
                Vec_IntSize(pAbc->vIndFlops), Abc_NtkLatchNum(pNtk) );
            return 0;
        }
        // modify the current network
        if ( !Abc_NtkMfsAfterICheck( pNtk, pAbc->nIndFrames, nFramesAdd, pAbc->vIndFlops, pPars ) )
        {
            Abc_Print( -1, "Resynthesis has failed.\n" );
            return 1;
        }
        if ( fUseAllFfs )
        {
            pAbc->nIndFrames = 0;
            Vec_IntFreeP( &pAbc->vIndFlops );
        }
    }
    else
    {
        // modify the current network
        if ( !Abc_NtkPerformMfs( pNtk, pPars ) )
        {
            Abc_Print( -1, "Resynthesis has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: mfs2 [-WFDMLCZNI <num>] [-daeijlvwh]\n" );
    Abc_Print( -2, "\t           performs don't-care-based optimization of logic networks\n" );
    Abc_Print( -2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             pPars->nTfoLevMax );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                pPars->nFanoutMax );
    Abc_Print( -2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n",                   pPars->nDepthMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    pPars->nWinSizeMax );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   pPars->nBTLimit );
    Abc_Print( -2, "\t-Z <num> : treat the first <num> logic nodes as fixed (0 = none) [default = %d]\n",       pPars->nFirstFixed );
    Abc_Print( -2, "\t-N <num> : the max number of nodes to try (0 = all) [default = %d]\n",                    pPars->nNodesMax );
    Abc_Print( -2, "\t-d       : toggle performing redundancy removal [default = %s]\n",                        pPars->fRrOnly? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n",                        pPars->fArea? "area": "area+edges" );
    Abc_Print( -2, "\t-e       : toggle high-effort resubstitution [default = %s]\n",                           pPars->fMoreEffort? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggle using inductive don't-cares [default = %s]\n",                          fIndDCs? "yes": "no" );
    Abc_Print( -2, "\t-j       : toggle using all flops when \"-i\" is enabled [default = %s]\n",               fUseAllFfs? "yes": "no" );
    Abc_Print( -2, "\t-I       : the number of additional frames inserted [default = %d]\n",                    nFramesAdd );
    Abc_Print( -2, "\t-l       : toggle deriving don't-cares [default = %s]\n",                                 pPars->fUseDcs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
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
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int RS_CUT_MIN =  4;
    int RS_CUT_MAX = 16;
    int c;
    int nCutsMax;
    int nNodesMax;
    int nLevelsOdc;
    int nMinSaved;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    int Log2Probs;
    int Log2Divs;
    extern int Abc_NtkResubstitute( Abc_Ntk_t * pNtk, int nCutsMax, int nNodesMax, int nMinSaved, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int Log2Probs, int Log2Divs );

    // set defaults
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;
    nMinSaved    =  1;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fVerbose     =  0;
    fVeryVerbose =  0;
    Log2Probs    =  0;
    Log2Divs     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNMFlzvwhPDV" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
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
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodesMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nMinSaved = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMinSaved < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelsOdc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelsOdc < 0 )
                goto usage;
            break;

        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Log2Probs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Log2Probs < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            Log2Divs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Log2Divs < 0 )
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
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
        case 'w':
            fVeryVerbose ^= 1;
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

    // modify the current network
    if ( !Abc_NtkResubstitute( pNtk, nCutsMax, nNodesMax, nMinSaved, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose, Log2Probs, Log2Divs ) )
    {
        Abc_Print( -1, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: resub [-KNMF <num>] [-lzvwh] [-PDV <num>]\n" );
    Abc_Print( -2, "\t           performs technology-independent restructuring of the AIG\n" );
    Abc_Print( -2, "\t-K <num> : the max cut size (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );
    Abc_Print( -2, "\t-N <num> : the max number of nodes to add (0 <= num <= 3) [default = %d]\n", nNodesMax );
    Abc_Print( -2, "\t-M <num> : the min number of nodes saved after one step (0 <= num) [default = %d]\n", nMinSaved );
    Abc_Print( -2, "\t-F <num> : the number of fanout levels for ODC computation [default = %d]\n", nLevelsOdc );
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle verbose printout of ODC computation [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n\n");
    Abc_Print( -2, "\t           When command line options '-P num', '-D num', and '-V num' are used,\n");
    Abc_Print( -2, "\t           this command does not perform resubstitution; instead, it dumps a binary file\n");
    Abc_Print( -2, "\t           containing 2^P resub problems, each containing 2^D-2 divs with support size V,\n");
    Abc_Print( -2, "\t           while the last two divisors are the offset and the onset of the function\n");
    Abc_Print( -2, "\t           (by default, the functions are completely specified; to get functions with don't-cares,\n");
    Abc_Print( -2, "\t           the user has to use command-line option '-F num' to enable the limited ODC computation)\n");
    Abc_Print( -2, "\t-P <num> : the log2 of the number of problems to be dumped [default = %d]\n", Log2Probs );
    Abc_Print( -2, "\t-D <num> : the log2 of the number of divisors to be collected (4 <= num <= 7) [default = %d]\n", Log2Divs );
    Abc_Print( -2, "\t-V <num> : the support size of the function (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandResubUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManResubUnateOne( char * pFileName, int nLimit, int nDivMax, int fWriteSol, int fVerbose );
    Gia_Man_t * pTemp;
    int nLimit    = 16;
    int nDivMax   = 50;
    int fWriteSol =  0;
    int fVerbose  =  0, c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LDsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimit < 0 )
                goto usage;
            break;   
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDivMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDivMax < 0 )
                goto usage;
            break;                        
        case 's':
            fWriteSol ^= 1;
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
        Abc_Print( -1, "Input file should be given on the command line.\n" );
        return 1;
    }
    pTemp = Gia_ManResubUnateOne( argv[globalUtilOptind], nLimit, nDivMax, fWriteSol, fVerbose );
    if ( pTemp )
    {
        Aig_Man_t * pMan = Gia_ManToAig( pTemp, 0 );
        Abc_Ntk_t * pNtk = Abc_NtkFromAigPhase( pMan );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
        Aig_ManStop( pMan );
        Gia_ManStop( pTemp );
        return 0;
    }
    Abc_Print( 0, "The networks is not generated.\n" );    
    return 0;

usage:
    Abc_Print( -2, "usage: resub_unate [-LD <num>] [-svh] <file>\n" );
    Abc_Print( -2, "\t         solves one instance of the resub problem\n" );
    Abc_Print( -2, "\t-L num : the limit on the number of nodes [default = %d]\n",                  nLimit );
    Abc_Print( -2, "\t-D num : the maximum number of binate divisors to consider [default = %d]\n", nDivMax );
    Abc_Print( -2, "\t-s     : toggle saving the result in the input file [default = %s]\n",        fWriteSol? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n",                           fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : resub problem file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandResubCore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Supp_ManSolveOne( char * pFileName, int nIters, int nRounds, int fWriteSol, int fVerbose );
    Gia_Man_t * pTemp;
    int nIters    = 1;
    int nRounds   = 1;
    int fWriteSol = 0;
    int fVerbose  = 0, c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IRsvh" ) ) != EOF )
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
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 )
                goto usage;
            break;                        
        case 's':
            fWriteSol ^= 1;
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
        Abc_Print( -1, "Input file should be given on the command line.\n" );
        return 1;
    }
    pTemp = Supp_ManSolveOne( argv[globalUtilOptind], nIters, nRounds, fWriteSol, fVerbose );
    if ( pTemp )
    {
        Aig_Man_t * pMan = Gia_ManToAig( pTemp, 0 );
        Abc_Ntk_t * pNtk = Abc_NtkFromAigPhase( pMan );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
        Aig_ManStop( pMan );
        Gia_ManStop( pTemp );
        return 0;
    }
    Abc_Print( 0, "The networks is not generated.\n" );    
    return 0;

usage:
    Abc_Print( -2, "usage: resub_core [-IR <num>] [-svh] <file>\n" );
    Abc_Print( -2, "\t         solves one instance of the resub problem\n" );
    Abc_Print( -2, "\t-I num : the number of iterations [default = %d]\n",                   nIters );
    Abc_Print( -2, "\t-R num : the number of rounds in each iteration [default = %d]\n",     nRounds );
    Abc_Print( -2, "\t-s     : toggle saving the result in the input file [default = %s]\n", fWriteSol? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n",                    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : resub problem file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandResubCheck( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Res6_ManResubCheck( char * pFileNameRes, char * pFileNameSol, int fVerbose );
    extern void Res6_ManResubCheckPla( char * pFileName, int fVerbose );
    char * pFileR = NULL, * pFileS = NULL;
    int fVerbose = 0, c;
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
    if ( argc == globalUtilOptind + 2 )
    {
        pFileR = argv[globalUtilOptind];
        pFileS = argv[globalUtilOptind+1];
    }
    else if ( argc == globalUtilOptind + 1 )
    {
        pFileR = argv[globalUtilOptind];
        pFileS = NULL;
    }
    else 
    {
        Abc_Print( -1, "Incorrect number of command line arguments.\n" );
        return 1;
    }
    if ( !strcmp(pFileR + strlen(pFileR) - 3, "pla") )
        Res6_ManResubCheckPla( pFileR, fVerbose );
    else
        Res6_ManResubCheck( pFileR, pFileS, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: resub_check [-vh] <file1> <file2>\n" );
    Abc_Print( -2, "\t           checks solution to a resub problem\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t<file1>  : resub problem file name\n");
    Abc_Print( -2, "\t<file2>  : (optional) solution file name\n");
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SimRsb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManSimRsb( Gia_Man_t * p, int nCands, int fVerbose );
    int c, nCands = 32, fVerbose = 0;
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
            nCands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCands < 0 )
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
        Abc_Print( -1, "Abc_CommandAbc9SimRsb(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9SimRsb(): This command works only for combinational AIGs.\n" );
        return 0;
    }
    if ( pAbc->pGia->vSimsPi == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SimRsb(): Does not have simulation information available.\n" );
        return 0;
    }
    Gia_ManSimRsb( pAbc->pGia, nCands, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &simrsb [-N num] [-vh]\n" );
    Abc_Print( -2, "\t         performs resubstitution\n" );
    Abc_Print( -2, "\t-C num : the number of candidates to try [default = %d]\n", nCands );
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
int Abc_CommandAbc9Resub( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManResub1( char * pFileName, int nNodes, int nSupp, int nDivs, int iChoice, int fUseXor, int fVerbose, int fVeryVerbose );
    extern Gia_Man_t * Gia_ManResub2( Gia_Man_t * pGia, int nNodes, int nSupp, int nDivs, int iChoice, int fUseXor, int fVerbose, int fVeryVerbose );
    Gia_Man_t * pTemp;
    int nNodes       =  0;
    int nSupp        =  0;
    int nDivs        =  0;
    int c, fVerbose  =  0;
    int fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSDvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-N\" should be followed by a floating point number.\n" );
                return 0;
            }
            nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodes < 0 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-S\" should be followed by a floating point number.\n" );
                return 0;
            }
            nSupp = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSupp < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( 1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                return 0;
            }
            nDivs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDivs < 0 )
                goto usage;
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
    if ( argc == globalUtilOptind + 1 )
    {
        pTemp = Gia_ManResub1( argv[globalUtilOptind], nNodes, nSupp, nDivs, 0, 0, fVerbose, fVeryVerbose );
        Abc_FrameUpdateGia( pAbc, pTemp );
        return 0;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Resub(): There is no AIG.\n" );
        return 1;
    }
    pTemp = Gia_ManResub2( pAbc->pGia, nNodes, nSupp, nDivs, 0, 0, fVerbose, fVeryVerbose );
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &resub [-NSD num] [-vwh]\n" );
    Abc_Print( -2, "\t           performs AIG resubstitution\n" );
    Abc_Print( -2, "\t-N num   : the limit on added nodes (num >= 0) [default = %d]\n",     nNodes );
    Abc_Print( -2, "\t-S num   : the limit on support size (num > 0) [default = %d]\n",     nSupp );
    Abc_Print( -2, "\t-D num   : the limit on divisor count (num > 0) [default = %d]\n",    nDivs );
    Abc_Print( -2, "\t-v       : toggles printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggles printing additional information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resubstitutes an AIG using compact windows and reusable proofs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Resub2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pNew;
    int c, fKeepLevel = 1, fVerbose = 0, nCutMax = 8, nSteps = 1, nMinSaved = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KNMlvh")) != EOF )
    {
        switch ( c )
        {
        case 'K':
        case 'N':
        case 'M':
        {
            char * pEnd, * pArg;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            pArg = argv[globalUtilOptind++];
            Value = strtol(pArg, &pEnd, 10);
            if ( pEnd == pArg || *pEnd || Value < 0 || Value > 1000000 ) goto usage;
            if ( c == 'K' ) { if ( Value < 4 || Value > 16 ) goto usage; nCutMax = (int)Value; }
            if ( c == 'N' ) { if ( Value > 1 ) goto usage; nSteps = (int)Value; }
            if ( c == 'M' ) { if ( Value < 1 ) goto usage; nMinSaved = (int)Value; }
            break;
        }
        case 'l': fKeepLevel ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "&resub2: There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManHasChoices(pAbc->pGia) || pAbc->pGia->pMuxes || Gia_ManXorNum(pAbc->pGia) || Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&resub2: This command requires an AIG without choices, XOR/MUX nodes, or barrier buffers.\n" );
        return 1;
    }
    if ( Gia_ManIsSeqWithBoxes(pAbc->pGia) && !Gia_ManIsNormalized(pAbc->pGia) )
    {
        Abc_Print( -1, "&resub2: Sequential AIGs with timing boxes must be normalized.\n" );
        return 1;
    }
    if ( Gia_ManObjNum(pAbc->pGia) > Gie_ObjectLimit() / 2 )
    {
        Abc_Print( -1, "&resub2: The AIG exceeds the mutable-graph object limit.\n" );
        return 1;
    }
    pNew = Rsub_ManPerform( pAbc->pGia, nCutMax, nSteps, nMinSaved, fKeepLevel, fVerbose );
    if ( pNew == NULL )
    {
        Abc_Print( -1, "&resub2: Resubstitution has failed.\n" );
        return 1;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: &resub2 [-KNM num] [-lvh]\n" );
    Abc_Print( -2, "\t         performs one pass of AIG resubstitution\n" );
    Abc_Print( -2, "\t-K num : maximum cut size (4 to 16) [default = %d]\n", nCutMax );
    Abc_Print( -2, "\t-N num : maximum new nodes (0 or 1) [default = %d]\n", nSteps );
    Abc_Print( -2, "\t-M num : minimum nodes saved [default = %d]\n", nMinSaved );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fKeepLevel ? "yes" : "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Mfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManPerformMfs( Gia_Man_t * p, Sfm_Par_t * pPars );
    Gia_Man_t * pTemp; int c;
    Sfm_Par_t Pars, * pPars = &Pars;
    Sfm_ParSetDefault( pPars );
    pPars->nTfoLevMax  =    5;
    pPars->nDepthMax   =  100;
    pPars->nWinSizeMax = 2000;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFDMLCNdaeblvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfoLevMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfoLevMax < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFanoutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFanoutMax < 0 )
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinSizeMax < 0 )
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY )
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
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNodesMax < 0 )
                goto usage;
            break;
        case 'd':
            pPars->fRrOnly ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'e':
            pPars->fMoreEffort ^= 1;
            break;
        case 'b':
            pPars->fAllBoxes ^= 1;
            break;
        case 'l':
            pPars->fUseDcs ^= 1;
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
        Abc_Print( -1, "Abc_CommandAbc9Mfs(): There is no AIG.\n" );
        return 0;
    }
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Mfs(): This command does not work with barrier buffers.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9Mfs(): The current AIG has no mapping.\n" );
        return 0;
    }
    if ( Gia_ManLutSizeMax(pAbc->pGia) > 15 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Mfs(): The current mapping has nodes with more than 15 inputs. Cannot use \"mfs\".\n" );
        return 0;
    }
//    if ( pAbc->pGia->pAigExtra && Gia_ManPiNum(pAbc->pGia->pAigExtra) > 6 )
//    {
//        Abc_Print( -1, "Abc_CommandAbc9Mfs(): The current white-boxes have more than 6 inputs. Cannot use \"mfs\".\n" );
//        return 0;
//    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
        pTemp = Gia_ManPerformMfs( pAbc->pGia, pPars );
    else
    {
        int nRegs = Gia_ManRegNum(pAbc->pGia);
        pAbc->pGia->nRegs = 0;
        pTemp = Gia_ManPerformMfs( pAbc->pGia, pPars );
        Gia_ManSetRegNum( pAbc->pGia, nRegs );
        if ( pTemp )
            Gia_ManSetRegNum( pTemp, nRegs );
    }
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &mfs [-WFDMLCN <num>] [-daeblvwh]\n" );
    Abc_Print( -2, "\t           performs don't-care-based optimization of logic networks\n" );
    Abc_Print( -2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             pPars->nTfoLevMax );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                pPars->nFanoutMax );
    Abc_Print( -2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n",                   pPars->nDepthMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    pPars->nWinSizeMax );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   pPars->nBTLimit );
    Abc_Print( -2, "\t-N <num> : the max number of nodes to try (0 = all) [default = %d]\n",                    pPars->nNodesMax );
    Abc_Print( -2, "\t-d       : toggle performing redundancy removal [default = %s]\n",                        pPars->fRrOnly? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n",                        pPars->fArea? "area": "area+edges" );
    Abc_Print( -2, "\t-e       : toggle high-effort resubstitution [default = %s]\n",                           pPars->fMoreEffort? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggle preserving all white boxes [default = %s]\n",                           pPars->fAllBoxes? "yes": "no" );
    Abc_Print( -2, "\t-l       : toggle deriving don't-cares [default = %s]\n",                                 pPars->fUseDcs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Mfsd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Sbd_NtkPerform( Gia_Man_t * pGia, Sbd_Par_t * pPars );
    Gia_Man_t * pTemp; int c;
    Sbd_Par_t Pars, AreaPars, * pPars = &Pars;
    Sbd_ParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KSNPRWFMCBamcdepAqvwh" ) ) != EOF )
    {
        if ( strchr("KSNPRWFMCB", c) && globalUtilOptind < argc )
        {
            char * pEnd;
            long Value;
            errno = 0;
            Value = strtol( argv[globalUtilOptind], &pEnd, 10 );
            if ( errno == ERANGE || pEnd == argv[globalUtilOptind] || *pEnd || Value < (c == 'R' ? 1 : 0) || Value > INT_MAX )
            {
                Abc_Print( -1, "Command line switch \"-%c\" requires a %s integer.\n", c, c == 'R' ? "positive" : "nonnegative" );
                goto usage;
            }
        }
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 2 || pPars->nLutSize > 6 )
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutNum < 1 || pPars->nLutNum > 3 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutSize < 2 || pPars->nCutSize > 10 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutNum = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutNum < 2 || pPars->nCutNum > 500 )
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfoLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfoLevels < 0 )
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTfoFanMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTfoFanMax < 1 )
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinSizeMax < 0 )
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
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimitDch = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIters < 1 )
                goto usage;
            break;
        case 'q':
            pPars->fChoices = 1;
            break;
        case 'a':
            pPars->fArea = 1;
            break;
        case 'm':
            pPars->fMapping ^= 1;
            break;
        case 'c':
            pPars->fMoreCuts ^= 1;
            break;
        case 'd':
            pPars->fDelay = 1;
            break;
        case 'e':
            pPars->fFindDivs ^= 1;
            break;
        case 'p':
            pPars->fUsePath = 1;
            break;
        case 'A':
            pPars->fUsePath = 0;
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
        Abc_Print( -1, "&mfs2: There is no AIG.\n" );
        return 1;
    }
    if ( globalUtilOptind != argc || pPars->nCutSize < pPars->nLutSize )
        goto usage;
    if ( pPars->fArea && pPars->fDelay )
    {
        Abc_Print( -1, "Area-only (-a) and delay (-d) modes cannot be combined.\n" );
        return 1;
    }
    if ( Gia_ManBufNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&mfs2: This command does not work with barrier buffers.\n" );
        return 1;
    }
    pTemp = Sbd_NtkPerform( pAbc->pGia, pPars );
    if ( pTemp == NULL )
        return 1;
    Abc_FrameUpdateGia( pAbc, pTemp );
    return 0;

usage:
    AreaPars = Pars;
    AreaPars.fDelay = 0;
    Sbd_ParResolve( &AreaPars );
    Sbd_ParResolve( pPars );
    Abc_Print( -2, "usage: &mfs2 [-KSNPRWFMCB <num>] [-amcdepAqvwh]\n" );
    Abc_Print( -2, "\t           performs SAT-based LUT optimization and remapping\n" );
    Abc_Print( -2, "\t           default: minimize LUT count without increasing the input LUT depth\n" );
    Abc_Print( -2, "\t           delay mode includes structural choices and a final SAT/IF area pass\n" );
    Abc_Print( -2, "\t           unmapped inputs are first mapped with &if -K; input LUTs must fit K\n" );
    Abc_Print( -2, "\t           XAIG boxes are preserved; depth includes one level per box arc (levB)\n" );
    Abc_Print( -2, "\t-K <num> : the target LUT size (2 <= num <= 6) [default = %d]\n",                        pPars->nLutSize );
    Abc_Print( -2, "\t-S <num> : the LUT structure size for delay search (1 <= num <= 3) [default = %d]\n",     pPars->nLutNum );
    Abc_Print( -2, "\t-N <num> : the cut size for delay search (K <= num <= 10) [default = %d]\n",             pPars->nCutSize );
    Abc_Print( -2, "\t-P <num> : the number of cuts for delay search (2 <= num <= 500) [default = %d]\n",       pPars->nCutNum );
    Abc_Print( -2, "\t-R <num> : max complete delay-mode iterations (1 <= num) [default = %d]\n",              pPars->nIters );
    Abc_Print( -2, "\t           extra iterations require -d; stop unless depth or equal-depth LUT count improves\n" );
    Abc_Print( -2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             pPars->nTfoLevels );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                pPars->nTfoFanMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    pPars->nWinSizeMax );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   pPars->nBTLimit );
    if ( pPars->fDelay )
    {
        Abc_Print( -2, "\t           final area defaults: W=%d F=%d M=%d C=%d; explicit values apply to both profiles\n",
            AreaPars.nTfoLevels, AreaPars.nTfoFanMax, AreaPars.nWinSizeMax, AreaPars.nBTLimit );
    }
    Abc_Print( -2, "\t-B <num> : choice SAT conflicts (0 = no limit; also capped by -C) [default = %d]\n", pPars->nBTLimitDch );
    Abc_Print( -2, "\t           the choice budget does not limit delay search\n" );
    Abc_Print( -2, "\t-a       : minimize area without a depth constraint (incompatible with -d)\n" );
    Abc_Print( -2, "\t-d       : reduce depth, then minimize area under the achieved depth bound\n" );
    Abc_Print( -2, "\t-q       : add structural choices and a final SAT/IF area pass (included in -d)\n" );
    Abc_Print( -2, "\t-m       : toggle returning a LUT mapping [default = %s]\n",                           pPars->fMapping? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle using several cuts in delay search [default = %s]\n",                  pPars->fMoreCuts? "yes": "no" );
    Abc_Print( -2, "\t-e       : toggle extra divisor search in delay mode (formerly -d) [default = %s]\n",    pPars->fFindDivs? "yes": "no" );
    Abc_Print( -2, "\t-p       : restrict delay search to critical paths of the LUT mapping (default)\n" );
    Abc_Print( -2, "\t-A       : search all nodes in delay mode\n" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Handles exact window optimization.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9eSLIM( Abc_Frame_t * pAbc, int argc, char ** argv ) {
  extern void seteSLIMParams(eSLIM_ParamStruct* params);
  extern Gia_Man_t* applyeSLIM(Gia_Man_t * pGia, const eSLIM_ParamStruct* params);
  
  eSLIM_ParamStruct params;
  int c;
  Gia_Man_t * pTemp;
  seteSLIMParams(&params);
  params.aig = 1;
  Extra_UtilGetoptReset();
  while ( ( c = Extra_UtilGetopt( argc, argv, "CDIPRSTVWXZcfhistx" ) ) != EOF ) {
      switch ( c ) {
        case 'C':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
              goto usage;
          }
          params.approximate_relation = 1;
          params.relation_tfo_bound  = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.relation_tfo_bound < 0 )
              goto usage;
          if (globalUtilOptind < argc) {
            char *next;
            int tfi_bound = strtol (argv[globalUtilOptind], &next, 10);
            if (argv[globalUtilOptind] != next && *next == '\0') {
              params.generate_relation_with_tfi_limit = 1;
              params.relation_tfi_bound = tfi_bound;
              globalUtilOptind++;
              if (params.relation_tfi_bound < 0) {
                goto usage;
              }
            }
          }
          break;
        case 'D':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
              goto usage;
          }
          params.synthesis_approach = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.synthesis_approach < 0 ||  params.synthesis_approach > 3)
              goto usage;
          break;
        case 'I':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
              goto usage;
          }
          params.iterations = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.iterations < 0 )
              goto usage;
          break;
        case 'P':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-P\" should be followed by a float.\n" );
              goto usage;
          }
          params.expansion_probability = atof(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.expansion_probability <= 0 || params.expansion_probability > 1)
              goto usage;
          break;
        case 'R':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
              goto usage;
          }
          params.nruns = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.nruns < 1 )
              goto usage;
          break;
        case 'S':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
              goto usage;
          }
          params.subcircuit_max_size = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.subcircuit_max_size < 2 )
              goto usage;
          break;
        case 'T':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
              goto usage;
          }
          params.timeout = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.timeout < 1 )
              goto usage;
          break;
        case 'V':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
              goto usage;
          }
          params.verbosity_level = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.verbosity_level < 0 || params.verbosity_level > 3 )
              goto usage;
          break;
        case 'W':
          if ( globalUtilOptind + 1 >= argc)
          {
              Abc_Print( -1, "Command line switch \"-W\" should be followed by two integers.\n" );
              goto usage;
          }
          params.nWindows = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if (params.nWindows <= 0) 
            goto usage;
          params.window_size = atoi(argv[globalUtilOptind]);
          if (params.window_size <= 0)
            goto usage;
          globalUtilOptind++;
          break;
        case 'X':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
              goto usage;
          }
          params.additional_gates = atoi(argv[globalUtilOptind]);
          if ( params.additional_gates < 0 )
              goto usage;
          globalUtilOptind++;
          break;
        case 'Z':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
              goto usage;
          }
          params.fix_seed = 1;
          params.seed = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          break;
        case 'c' :
          params.criticial_path_selection_bias ^= 1;
          break;
        case 'f' :
          params.forward_search ^= 1;
          break;
        case 'h':
          goto usage;
        case 'i' :
          params.apply_inprocessing ^= 1;
          break;
        case 's' :
          params.fill_subcircuits ^= 1;
          break;
        case 't' :
          params.use_taboo_list ^= 1;
          break;
        case 'x' :
          params.aig = 0;
          break;
        default:
          goto usage;
      }
  }
  if (params.nWindows > 0 && params.synthesis_approach != 0) {
    Abc_Print( -1, "Windows can only be used with area minimization\n" );
    return 1;
  }
  if ( pAbc->pGia == NULL ) {
        Abc_Print( -1, "Abc_CommandAbc9Test(): There is no AIG.\n" );
        return 1;
  }

  pTemp = applyeSLIM(pAbc->pGia, &params);
  if (pTemp == NULL) {
    Abc_Print( -1, "eSLIM could not process the given circuit.\n" );
    return 1;
  }
    
  Abc_FrameUpdateGia( pAbc, pTemp );
  return 0;


  usage:
    seteSLIMParams(&params); // show the correct default values
    Abc_Print( -2, "usage: &eslim [-CDIPRSTVWXZ <num>] [-cfhistx]\n" );
    Abc_Print( -2, "\t           circuit optimization using exact synthesis and the SAT-based local improvement method (SLIM)\n" );
    Abc_Print( -2, "\t-C <num> : approximate Boolean relations by only considering the frist C levels in the cone \n");
    Abc_Print( -2, "\t-D <num> : the delay mode to use [default = %d]\n",  params.synthesis_approach );
    Abc_Print( -2, "\t-I <num> : the maximal number of iterations (0 = no limit) for the individual eSLIM runs [default = %d]\n",  params.iterations  );
    Abc_Print( -2, "\t-P <num> : the probability of expanding a node [default = %.2f]\n",    params.expansion_probability );
    Abc_Print( -2, "\t-R <num> : the number of runs of eSLIM + Inprocessing [default = %d]\n",    params.nruns );
    Abc_Print( -2, "\t-S <num> : the maximal size of considered subcircuits [default = %d]\n",    params.subcircuit_max_size );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds for the individual eSLIM runs [default = %d]\n",    params.timeout );
    Abc_Print( -2, "\t-V <num> : the verbosity level [default = %d]\n",       params.verbosity_level);
    Abc_Print( -2, "\t-W <num> <num> : Use m windows of size n [default = %d, %d]\n",       params.nWindows, params.window_size);
    Abc_Print( -2, "\t-X <num> : the maximal number of additional gates that may be used for depth optimization [default = %d]\n", params.additional_gates);
    Abc_Print( -2, "\t-Z <num> : use a fixed seed\n",       params.seed);
    Abc_Print( -2, "\t-c       : toggle bias for selection of nodes on the crictical path\n");
    Abc_Print( -2, "\t-f       : toggle forward expansion of root nodes\n");
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t-i       : toggle inprocessing\n");
    Abc_Print( -2, "\t-s       : toggle fill subcircuits\n");
    Abc_Print( -2, "\t-t       : toggle use taboo list\n");
    Abc_Print( -2, "\t-x       : allow xor-gates\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Franz-Xaver Reichl from University of Freiburg.\n" );

    return 1;

}

/**Function*************************************************************

  Synopsis    [Reads an unsigned command-line argument without wrapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

static int Es2_ReadUnsigned( const char * pText, unsigned int * pValue )
{
    char * pEnd;
    unsigned long Value;
    if ( *pText == '-' )
        return 0;
    errno = 0;
    Value = strtoul( pText, &pEnd, 10 );
    if ( pText == pEnd || *pEnd || errno == ERANGE || Value > UINT_MAX )
        return 0;
    *pValue = (unsigned int)Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Optimizes the current AIG using the eSLIM2 package.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

int Abc_CommandAbc9eSLIM2( Abc_Frame_t * pAbc, int argc, char ** argv ) {
  extern void seteSLIM2Params(eSLIM2_ParamStruct* params);
  extern Gia_Man_t* applyeSLIM2(Gia_Man_t * pGia, const eSLIM2_ParamStruct* params);

  eSLIM2_ParamStruct params;
  int c;
  Gia_Man_t * pTemp;
  seteSLIM2Params(&params);
  params.aig = 1;
  Extra_UtilGetoptReset();
  while ( ( c = Extra_UtilGetopt( argc, argv, "ABCDEIJPRSTVWXZcefghilmqstx" ) ) != EOF ) {
      switch ( c ) {
        case 'J':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.rewrite_mode) || params.rewrite_mode > 2)
            goto usage;
          break;
        case 'A':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.aig_encoding) || params.aig_encoding > 2)
            goto usage;
          break;
        case 'l':
          params.initial_depth_bound ^= 1;
          break;
        case 'm':
          params.mux_consensus ^= 1;
          break;
        case 'g':
          params.fast_simulation ^= 1;
          break;
        case 'q':
          params.tune_relation_solver ^= 1;
          break;
        case 'B':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.synthesis_timeout_ms))
            goto usage;
          break;
        case 'e':
          params.compact_timing ^= 1;
          break;
        case 'C':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
              goto usage;
          }
          params.approximate_relation = 1;
          params.relation_tfo_bound  = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.relation_tfo_bound < 0 )
              goto usage;
          if (globalUtilOptind < argc) {
            char *next;
            int tfi_bound = strtol (argv[globalUtilOptind], &next, 10);
            if (argv[globalUtilOptind] != next && *next == '\0') {
              params.generate_relation_with_tfi_limit = 1;
              params.relation_tfi_bound = tfi_bound;
              globalUtilOptind++;
              if (params.relation_tfi_bound < 0) {
                goto usage;
              }
            }
          }
          break;
        case 'D':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
              goto usage;
          }
          params.synthesis_approach = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.synthesis_approach < 0 ||  params.synthesis_approach > 3)
              goto usage;
          break;
        case 'I':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.iterations) )
              goto usage;
          globalUtilOptind++;
          break;
        case 'P':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.ncores) || !params.ncores) {
            Abc_Print( -1, "Command line switch \"-P\" requires a positive integer core limit.\n" );
            goto usage;
          }
          break;
        case 'E':
        {
          char * pEnd;
          const char * pText;
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-E\" should be followed by a probability.\n" );
              goto usage;
          }
          pText = argv[globalUtilOptind++];
          errno = 0;
          params.expansion_probability = strtod(pText, &pEnd);
          if (pText == pEnd || *pEnd || errno == ERANGE ||
              !(params.expansion_probability > 0 && params.expansion_probability <= 1))
              goto usage;
          break;
        }
        case 'R':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.nruns) )
              goto usage;
          globalUtilOptind++;
          if ( params.nruns < 1 )
              goto usage;
          break;
        case 'S':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.subcircuit_max_size) )
              goto usage;
          globalUtilOptind++;
          if ( params.subcircuit_max_size < 2 )
              goto usage;
          break;
        case 'T':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.timeout) )
              goto usage;
          globalUtilOptind++;
          if ( params.timeout < 1 )
              goto usage;
          break;
        case 'V':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
              goto usage;
          }
          params.verbosity_level = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.verbosity_level < 0 || params.verbosity_level > 3 )
              goto usage;
          break;
        case 'W':
        {
          unsigned int nWindows, nSize;
          if ( globalUtilOptind + 1 >= argc)
          {
              Abc_Print( -1, "Command line switch \"-W\" should be followed by two integers.\n" );
              goto usage;
          }
          if (!Es2_ReadUnsigned(argv[globalUtilOptind++], &nWindows) || !nWindows || nWindows > INT_MAX ||
              !Es2_ReadUnsigned(argv[globalUtilOptind++], &nSize) || !nSize || nSize > INT_MAX)
            goto usage;
          params.nWindows = (int)nWindows;
          params.window_size = (int)nSize;
          break;
        }
        case 'X':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.additional_gates) )
              goto usage;
          globalUtilOptind++;
          break;
        case 'Z':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
              goto usage;
          }
          params.fix_seed = 1;
          params.seed = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          break;
        case 'c' :
          params.criticial_path_selection_bias ^= 1;
          break;
        case 'f' :
          params.forward_search ^= 1;
          break;
        case 'h':
          goto usage;
        case 'i' :
          params.apply_inprocessing ^= 1;
          break;
        case 's' :
          params.fill_subcircuits ^= 1;
          break;
        case 't' :
          params.use_taboo_list ^= 1;
          break;
        case 'x' :
          params.aig = 0;
          break;
        default:
          goto usage;
      }
  }
  if ((params.nWindows > 0 || params.ncores > 1) && params.synthesis_approach > 1) {
    Abc_Print( -1, "Parallel windows require -D 0 (area) or -D 1 (area with a depth bound).\n" );
    return 1;
  }
  if (params.synthesis_approach == 1 && !params.aig) {
    Abc_Print( -1, "Mode 1 requires AND gates; -x counts XOR nodes rather than their exported AIG cost.\n" );
    return 1;
  }
  if ( Abc_FrameReadGia(pAbc) == NULL ) {
        Abc_Print( -1, "There is no AIG.\n" );
        return 1;
  }

  pTemp = applyeSLIM2(Abc_FrameReadGia(pAbc), &params);
  if (pTemp == NULL) {
    Abc_Print( -1, "eSLIM2 could not process the given circuit.\n" );
    return 1;
  }

  Abc_FrameUpdateGia( pAbc, pTemp );
  return 0;


  usage:
    seteSLIM2Params(&params); // show the correct default values
    Abc_Print( -2, "usage: &eslim2 [-ABCDEIJPRSTVWXZ <num>] [-cefghilmqstx]\n" );
    Abc_Print( -2, "\t           circuit optimization using exact synthesis and the SAT-based local improvement method (SLIM)\n" );
    Abc_Print( -2, "\t-A <num> : AIG encoding in mode 1: 0 = generic, 1 = ordered pins, 2 = ordered pins and gates [default = %u]\n", params.aig_encoding );
    Abc_Print( -2, "\t-B <num> : base SAT-call budget in milliseconds for mode 1 (0 = legacy allocation) [default = %u]\n", params.synthesis_timeout_ms );
    Abc_Print( -2, "\t           Existing-size searches receive 4x this budget; every 16th search receives another 10x.\n" );
    Abc_Print( -2, "\t-C <num> : approximate Boolean relations by only considering the first C levels in the cone \n");
    Abc_Print( -2, "\t-D <num> : delay mode: 0 = area, 1 = area with depth bound, 2 = area then depth, 3 = depth [default = %d]\n",  params.synthesis_approach );
    Abc_Print( -2, "\t           Mode 1 keeps both exported AIG node count and level count at most their input values.\n" );
    Abc_Print( -2, "\t           Area mode (0), including windows, may increase levels. Use mode 1 to preserve the input bound.\n" );
    Abc_Print( -2, "\t-E <prob>: the probability of expanding a node (formerly -P) [default = %.2f]\n", params.expansion_probability );
    Abc_Print( -2, "\t-I <num> : the maximal number of iterations (0 = no limit) for the individual eSLIM2 runs [default = %d]\n",  params.iterations  );
    Abc_Print( -2, "\t-J <num> : AIG rewriting in mode 1: 0 = off, 1 = initial, 2 = adaptive [default = %u]\n", params.rewrite_mode );
    Abc_Print( -2, "\t           Adaptive repeats every 2 seconds only if the initial pass removed nodes.\n" );
    Abc_Print( -2, "\t           Rewriting preserves size and depth and is disabled by -i.\n" );
    Abc_Print( -2, "\t           Windows disable -J and strash in both modes; -i controls final inprocessing.\n" );
    Abc_Print( -2, "\t-P <num> : maximum number of worker cores; 1 uses the serial command [default = %u]\n", params.ncores );
    Abc_Print( -2, "\t           More cores use automatic windows in modes 0/1; small designs may use fewer.\n" );
    Abc_Print( -2, "\t-R <num> : the number of runs of eSLIM2 + Inprocessing [default = %d]\n",    params.nruns );
    Abc_Print( -2, "\t-S <num> : the maximal size of considered subcircuits [default = %d]\n",    params.subcircuit_max_size );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds for the individual eSLIM2 runs [default = %d]\n",    params.timeout );
    Abc_Print( -2, "\t-V <num> : the verbosity level [default = %d]\n",       params.verbosity_level);
    Abc_Print( -2, "\t           Level 1 includes search/cache counters; level 2 adds SAT-call timings; level 3 adds per-size details.\n" );
    Abc_Print( -2, "\t-W <m> <n>: select up to m windows of n nodes instead of automatic partitioning\n" );
    Abc_Print( -2, "\t           Windows share the -T budget and use at most -P cores; -I applies per window.\n" );
    Abc_Print( -2, "\t-X <num> : the maximal number of additional gates that may be used for depth optimization [default = %d]\n", params.additional_gates);
    Abc_Print( -2, "\t-Z <num> : use a fixed seed\n");
    Abc_Print( -2, "\t-c       : toggle bias for selection of nodes on the critical path\n");
    Abc_Print( -2, "\t-e       : toggle compact encoding of the depth bound in mode 1 [default = %s]\n", params.compact_timing ? "yes" : "no" );
    Abc_Print( -2, "\t-f       : toggle forward expansion of root nodes\n");
    Abc_Print( -2, "\t-g       : toggle specialized gate simulation and Gray-code traversal [default = %s]\n", params.fast_simulation ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t-i       : toggle inprocessing (disabling it also disables mode-1 rewriting)\n");
    Abc_Print( -2, "\t-l       : toggle keeping the initial depth bound throughout mode 1 [default = %s]\n", params.initial_depth_bound ? "yes" : "no" );
    Abc_Print( -2, "\t           With this enabled, intermediate depth gains may be traded for area within the input depth.\n" );
    Abc_Print( -2, "\t-m       : toggle redundant mux clauses for two-input gates [default = %s]\n", params.mux_consensus ? "yes" : "no" );
    Abc_Print( -2, "\t-q       : toggle relation SAT tuning (disable lucky phases) [default = %s]\n", params.tune_relation_solver ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggle fill subcircuits\n");
    Abc_Print( -2, "\t-t       : toggle use taboo list\n");
    Abc_Print( -2, "\t-x       : allow xor-gates (not supported with -D 1)\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Franz-Xaver Reichl from University of Freiburg.\n" );

    return 1;

}

/**Function*************************************************************

  Synopsis    [Handles exact optimization of LUT networks.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9elSLIM( Abc_Frame_t * pAbc, int argc, char ** argv ) {
  extern void seteSLIMParams(eSLIM_ParamStruct* params);
  extern Abc_Ntk_t* applyelSLIM(Abc_Ntk_t * pGia, const eSLIM_ParamStruct* params);
  
  eSLIM_ParamStruct params;
  Abc_Ntk_t* pNtk, *pNtknew;
  int c;
  seteSLIMParams(&params);
  Extra_UtilGetoptReset();
  params.subcircuit_max_size = 4;
  while ( ( c = Extra_UtilGetopt( argc, argv, "CDGIPRSTVWXZcfhist" ) ) != EOF ) {
      switch ( c ) {
        case 'C':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
              goto usage;
          }
          params.approximate_relation = 1;
          params.relation_tfo_bound  = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.relation_tfo_bound < 0 )
              goto usage;
          if (globalUtilOptind < argc) {
            char *next;
            int tfi_bound = strtol (argv[globalUtilOptind], &next, 10);
            if (argv[globalUtilOptind] != next && *next == '\0') {
              params.generate_relation_with_tfi_limit = 1;
              params.relation_tfi_bound = tfi_bound;
              globalUtilOptind++;
              if (params.relation_tfi_bound < 0) {
                goto usage;
              }
            }
          }
          break;
        case 'D':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
              goto usage;
          }
          params.synthesis_approach = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.synthesis_approach < 0 ||  params.synthesis_approach > 3)
              goto usage;
          break;
        case 'I':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
              goto usage;
          }
          params.iterations = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.iterations < 0 )
              goto usage;
          break;
        case 'G':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
              goto usage;
          }
          params.gate_size = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.gate_size < 1 || params.gate_size > 6 )
              goto usage;
          break;
        case 'P':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-P\" should be followed by a float.\n" );
              goto usage;
          }
          params.expansion_probability = atof(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.expansion_probability <= 0 || params.expansion_probability > 1)
              goto usage;
          break;
        case 'R':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
              goto usage;
          }
          params.nruns = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.nruns < 1 )
              goto usage;
          break;
        case 'S':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
              goto usage;
          }
          params.subcircuit_max_size = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.subcircuit_max_size < 2 )
              goto usage;
          break;
        case 'T':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
              goto usage;
          }
          params.timeout = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.timeout < 1 )
              goto usage;
          break;
        case 'V':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
              goto usage;
          }
          params.verbosity_level = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.verbosity_level < 0 || params.verbosity_level > 3 )
              goto usage;
          break;
        case 'W':
          if ( globalUtilOptind + 1 >= argc)
          {
              Abc_Print( -1, "Command line switch \"-W\" should be followed by two integers.\n" );
              goto usage;
          }
          params.nWindows = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if (params.nWindows <= 0) 
            goto usage;
          params.window_size = atoi(argv[globalUtilOptind]);
          if (params.window_size <= 0)
            goto usage;
          globalUtilOptind++;
          break;
        case 'X':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
              goto usage;
          }
          params.additional_gates = atoi(argv[globalUtilOptind]);
          if ( params.additional_gates < 0 )
              goto usage;
          globalUtilOptind++;
          break;
        case 'Z':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
              goto usage;
          }
          params.fix_seed = 1;
          params.seed = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          break;
        case 'c' :
          params.criticial_path_selection_bias ^= 1;
          break;
        case 'f' :
          params.forward_search ^= 1;
          break;
        case 'h':
          goto usage;
        case 'i' :
          params.apply_inprocessing ^= 1;
          break;
        case 's' :
          params.fill_subcircuits ^= 1;
          break;
        case 't' :
          params.use_taboo_list ^= 1;
          break;
        default:
          goto usage;
      }
  }
  if (params.nWindows > 0 && params.synthesis_approach != 0) {
    Abc_Print( -1, "Windows can only be used with area minimization\n" );
    return 1;
  }

  pNtk = Abc_FrameReadNtk(pAbc);
  if ( pNtk == NULL )
  {
    Abc_Print( -1, "Empty network.\n" );
    return 1;
  }
  if ( !Abc_NtkIsLogic(pNtk) )
  {
    Abc_Print( -1, "This command can only be applied to a logic network.\n" );
    return 1;
  }
  if (!Abc_NtkHasSop(pNtk)) {
    Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
  }


  params.aig = 0;
  pNtknew = applyelSLIM(pNtk, &params);
  if (pNtknew == NULL) {
    Abc_Print( -1, "eSLIM could not process the given circuit.\n" );
    return 1;
  }
  Abc_FrameReplaceCurrentNetwork( pAbc, pNtknew );
    
  return 0;

  usage:
    seteSLIMParams(&params); // show the correct default values
    Abc_Print( -2, "usage: elslim [-CDGIPRSTVWXZ <num>] [-cfhist]\n" );
    Abc_Print( -2, "\t           Lut optimization using exact synthesis and the SAT-based local improvement method (SLIM)\n" );
    Abc_Print( -2, "\t-C <num> : approximate Boolean relations by only considering the frist C levels in the cone \n");
    Abc_Print( -2, "\t-D <num> : the delay mode to use [default = %d]\n",  params.synthesis_approach );
    Abc_Print( -2, "\t-G <num> : the maximal number of fanins gates may use (at most 6) [default = %d]\n",  params.gate_size  );
    Abc_Print( -2, "\t-I <num> : the maximal number of iterations (0 = no limit) for the individual eSLIM runs [default = %d]\n",  params.iterations  );
    Abc_Print( -2, "\t-P <num> : the probability of expanding a node [default = %.2f]\n",    params.expansion_probability );
    Abc_Print( -2, "\t-R <num> : the number of runs of eSLIM + Inprocessing [default = %d]\n",    params.nruns );
    Abc_Print( -2, "\t-S <num> : the maximal size of considered subcircuits [default = %d]\n",    params.subcircuit_max_size );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds for the individual eSLIM runs [default = %d]\n",    params.timeout );
    Abc_Print( -2, "\t-V <num> : the verbosity level [default = %d]\n",       params.verbosity_level);
    Abc_Print( -2, "\t-W <num> <num> : Use m windows of size n [default = %d, %d]\n",       params.nWindows, params.window_size);
    Abc_Print( -2, "\t-X <num> : the maximal number of additional gates that may be used for depth optimization [default = %d]\n", params.additional_gates);
    Abc_Print( -2, "\t-Z <num> : use a fixed seed\n",       params.seed);
    Abc_Print( -2, "\t-c       : toggle bias for selection of nodes on the crictical path\n");
    Abc_Print( -2, "\t-f       : toggle forward expansion of root nodes\n");
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t-i       : toggle inprocessing\n");
    Abc_Print( -2, "\t-s       : toggle fill subcircuits\n");
    Abc_Print( -2, "\t-t       : toggle use taboo list\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Franz-Xaver Reichl from University of Freiburg.\n" );

    return 1;

}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
