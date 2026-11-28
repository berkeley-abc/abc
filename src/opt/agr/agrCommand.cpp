/**CFile****************************************************************

  FileName    [agrCommand.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Command agr.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrCommand.cpp,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "agr.h"
#include "agrInt.h"

#include <algorithm>
#include <cerrno>
#include <cmath>
#include <cstdlib>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Parses a finite positive number.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Agr_ParsePositive( const char * pText, double * pValue )
{
    char * pEnd = NULL;
    double Value;
    errno = 0;
    Value = std::strtod( pText, &pEnd );
    if ( errno || pEnd == pText || *pEnd || !std::isfinite(Value) || Value <= 0.0 )
        return 0;
    *pValue = Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints the usage of command agr.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Agr_PrintUsage( void )
{
    Abc_Print( -2, "usage: agr [-S <num>] [-vh]\n" );
    Abc_Print( -2, "\t           adaptive geometric restructuring of a combinational AIG\n" );
    Abc_Print( -2, "\t-S <num> : initial placement step in bin widths [default = %g]\n", PA_PLACE_STEP );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = no]\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           For example, command line \"agr -S 0.30\"\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           This command was contributed by Anqi Lu from UC Berkeley.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Places the AIG and runs the AGR block twice.]

  Description [Places the AIG and runs the block twice; returns 0 on
               success.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Agr_Restructure( Abc_Frame_t * pAbc, Abc_Ntk_t * pNtk, double Step, double * pPlacedHpwl )
{
    if ( !Pa_ManPlace( pNtk, Step ) || !Pa_ManReadMetrics( pNtk, pPlacedHpwl, NULL, NULL, NULL ) )
        return 1;
    for ( int Block = 0; Block < 2; ++Block )
    {
        const int nRoots = std::max( 1, (int)std::ceil( 4.0 * std::sqrt( (double)Abc_NtkNodeNum(pNtk) ) ) );
        if ( Agr_RunBlock( pAbc, nRoots ) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Command agr.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Agr_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pBackup, * pResult;
    double Step = PA_PLACE_STEP, PlacedHpwl = 0.0, FinalHpwl = 0.0;
    int c, fVerbose = 0, nNodes, RetValue;
    abctime clk = Abc_Clock();
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive number.\n" );
                return Agr_PrintUsage();
            }
            if ( !Agr_ParsePositive( argv[globalUtilOptind++], &Step ) )
            {
                Abc_Print( -1, "agr: the placement step must be finite and positive.\n" );
                return 1;
            }
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            return Agr_PrintUsage();
        }
    }
    if ( globalUtilOptind != argc )
        return Agr_PrintUsage();
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "agr: there is no current network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) || Abc_NtkLatchNum(pNtk) || Abc_NtkGetChoiceNum(pNtk) ||
         pNtk->pExdc || pNtk->pExcare || pNtk->pManTime )
    {
        Abc_Print( -1, "agr: the current network must be a combinational AIG without choices or constraints.\n" );
        return 1;
    }
    // an AIG without internal nodes has nothing to restructure
    if ( Abc_NtkNodeNum(pNtk) == 0 )
        return 0;
    nNodes = Abc_NtkNodeNum(pNtk);
    pBackup = Abc_NtkDup( pNtk );
    Agr_SetVerbose( fVerbose );
    // AGR's evaluator settings; PA commands run with all of them off.
    Pa_ManSetCapacityRepair( 1 );
    Pa_ManSetWireTolerance( 1 );
    RetValue = Agr_Restructure( pAbc, pNtk, Step, &PlacedHpwl );
    Agr_ResetBlock();
    Pa_ManSetWireTolerance( 0 );
    Pa_ManSetCapacityRepair( 0 );
    Pa_ManSetPhysicalAreaGuard( 0 );
    Pa_ManSetTimingEvaluation( 0 );
    if ( RetValue == 0 )
        Pa_ManReadMetrics( pNtk, &FinalHpwl, NULL, NULL, NULL );
    Pa_ManClearPlacement();
    Agr_SetVerbose( 0 );
    // The block edits the network in place; strashing restores ABC's
    // topological object order.
    pResult = RetValue == 0 ? Abc_NtkStrash( pNtk, 0, 1, 0 ) : NULL;
    if ( pResult == NULL )
    {
        Abc_FrameReplaceCurrentNetwork( pAbc, pBackup );
        Abc_Print( -1, "agr: restructuring failed; the original network is restored.\n" );
        return 1;
    }
    Abc_NtkDelete( pBackup );
    Abc_FrameReplaceCurrentNetwork( pAbc, pResult );
    if ( fVerbose )
        Abc_Print( 1, "agr: nodes %d -> %d  HPWL %.3f -> %.3f  time %.2f sec\n", nNodes,
                   Abc_NtkNodeNum(pResult), PlacedHpwl, FinalHpwl, 1.0 * (Abc_Clock() - clk) / CLOCKS_PER_SEC );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Registers command agr.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Agr_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Physical synthesis", "agr", Agr_Command, 1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
