/**CFile****************************************************************

  FileName    [paCommands.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Commands pa_place, pa_stats, pa_rs, pa_rw, pa_rf and pa_strash.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paCommands.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "pa.h"
#include "paInt.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pa_Man_t_ Pa_Man_t;
struct Pa_Man_t_
{
    void *         pState[PA_STATE_NUM];
    void        (* pFree[PA_STATE_NUM])( void * );
};

typedef int (*Pa_Operator_t)( Abc_Ntk_t * pNtk );

// PA's operators visit every node and put the nodes into DFS order at the end.
static int Pa_Resubstitute( Abc_Ntk_t * pNtk ) { return Pa_NtkResubstitute( pNtk, NULL, 1, 0 ); }
static int Pa_Rewrite( Abc_Ntk_t * pNtk )      { return Pa_NtkRewrite( pNtk, NULL, 1 );         }
static int Pa_Refactor( Abc_Ntk_t * pNtk )     { return Pa_NtkRefactor( pNtk, NULL, 1 );        }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prints the acknowledgment of the PA commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_PrintAcknowledgment( void )
{
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           This command was contributed by Anqi Lu from UC Berkeley.\n" );
    Abc_Print( -2, "\t           The paper describing the method: \"Placement-aware logic optimization\",\n" );
    Abc_Print( -2, "\t           Proc. DATE 2027.\n" );
}

/**Function*************************************************************

  Synopsis    [Prints the node count, HPWL and overflow of the current placement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_PrintMetrics( const char * pName, Abc_Ntk_t * pNtk )
{
    double Hpwl = 0.0, Overflow = 0.0;
    Pa_ManReadMetrics( pNtk, &Hpwl, &Overflow, NULL, NULL );
    Abc_Print( 1, "%s: nodes = %d  HPWL = %.3f  overflow = %.4f\n", pName, Abc_NtkNodeNum(pNtk), Hpwl, Overflow );
}

/**Function*************************************************************

  Synopsis    [Command pa_place.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandPlace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v': fVerbose ^= 1; break;
        default:  goto usage;
        }
    }
    if ( globalUtilOptind != argc )
        goto usage;
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "pa_place: there is no current network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) && !Abc_NtkHasMapping(pNtk) )
    {
        Abc_Print( -1, "pa_place: the current network must be a strashed AIG or a mapped network.\n" );
        return 1;
    }
    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        Abc_Print( -1, "pa_place: the current network has no internal nodes.\n" );
        return 1;
    }
    Pa_ManPlace( pNtk, PA_PLACE_STEP );
    if ( fVerbose )
        Pa_PrintMetrics( "pa_place", pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: pa_place [-vh]\n" );
    Abc_Print( -2, "\t           places the current AIG or mapped network for pa_rs, pa_rw and pa_rf\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = no]\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           For example, command line \"pa_place; pa_rs; pa_rw; pa_rf\"\n" );
    Pa_PrintAcknowledgment();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Command pa_stats.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandStats( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
        goto usage;
    if ( globalUtilOptind != argc )
        goto usage;
    if ( pNtk == NULL || !Pa_ManHasPlacement(pNtk) )
    {
        Abc_Print( -1, "pa_stats: the current network has no placement; run pa_place.\n" );
        return 1;
    }
    Pa_PrintMetrics( "pa_stats", pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: pa_stats [-h]\n" );
    Abc_Print( -2, "\t           prints the HPWL and density overflow of the current placement\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Pa_PrintAcknowledgment();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs one placement-aware operator on the current AIG.]

  Description [Runs one placement-aware operator. On failure the original
               network is restored and the placement is cleared.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_RunOperator( Abc_Frame_t * pAbc, int argc, char ** argv, const char * pName,
                           const char * pWhat, Pa_Operator_t Operator )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pDup;
    int c, fCluster = 0, fVerbose = 0, RetValue;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c': fCluster ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        default:  goto usage;
        }
    }
    if ( globalUtilOptind != argc )
        goto usage;
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "%s: there is no current network.\n", pName );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) || Abc_NtkLatchNum(pNtk) || Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "%s: the current network must be a combinational AIG without choices.\n", pName );
        return 1;
    }
    if ( !Pa_ManHasPlacement(pNtk) )
    {
        Abc_Print( -1, "%s: the current AIG has no placement; run pa_place.\n", pName );
        return 1;
    }
    if ( fCluster && !Pa_ManHasInheritedPlacement(pNtk) )
    {
        Abc_Print( -1, "%s -c: requires a placed mapped network followed by pa_strash.\n", pName );
        return 1;
    }
    pDup = Abc_NtkDup( pNtk );
    Pa_ManSetClusterEvaluation( fCluster );
    Pa_ManSetTimingEvaluation( 1 );
    RetValue = Operator( pNtk );
    Pa_ManSetTimingEvaluation( 0 );
    Pa_ManSetClusterEvaluation( 0 );
    if ( RetValue <= 0 )
    {
        Pa_ManClearPlacement();
        Abc_FrameReplaceCurrentNetwork( pAbc, pDup );
        Abc_Print( -1, "%s: failed; the original network is restored.\n", pName );
        return 1;
    }
    Abc_NtkDelete( pDup );
    if ( fVerbose )
        Pa_PrintMetrics( pName, pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: %s [-cvh]\n", pName );
    Abc_Print( -2, "\t           placement-aware %s of the placed AIG\n", pWhat );
    Abc_Print( -2, "\t-c       : toggle snapping new nodes to the mapped-cell clusters inherited by pa_strash [default = no]\n" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = no]\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           For example, command line \"pa_place; %s\"\n", pName );
    Pa_PrintAcknowledgment();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Command pa_rs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandResubstitute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    return Pa_RunOperator( pAbc, argc, argv, "pa_rs", "resubstitution (8-input cuts, up to two new nodes)", Pa_Resubstitute );
}

/**Function*************************************************************

  Synopsis    [Command pa_rw.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    return Pa_RunOperator( pAbc, argc, argv, "pa_rw", "rewriting (4-input cuts)", Pa_Rewrite );
}

/**Function*************************************************************

  Synopsis    [Command pa_rf.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    return Pa_RunOperator( pAbc, argc, argv, "pa_rf", "refactoring (10-input nodes, 16-input cones)", Pa_Refactor );
}

/**Function*************************************************************

  Synopsis    [Command pa_strash.]

  Description [strash that gives every new AIG node the center of the
               mapped cell that produced it, when the mapped network is
               placed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_CommandStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c, fTransfer;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
        goto usage;
    if ( globalUtilOptind != argc )
        goto usage;
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "pa_strash: there is no current network.\n" );
        return 1;
    }
    // Capture the cell centers before strashing replaces the gate data.
    fTransfer = Abc_NtkHasMapping(pNtk) && Pa_ManHasPlacement(pNtk);
    if ( fTransfer && !Pa_ManBeginMappedUnmap(pNtk) )
    {
        Abc_Print( -1, "pa_strash: failed to capture the mapped placement.\n" );
        return 1;
    }
    pNtkRes = Pa_NtkStrash( pNtk );
    if ( pNtkRes == NULL )
    {
        Pa_ManAbortMappedUnmap();
        Abc_Print( -1, "pa_strash: strashing has failed.\n" );
        return 1;
    }
    if ( fTransfer && !Pa_ManFinishMappedUnmap(pNtkRes) )
    {
        Pa_ManAbortMappedUnmap();
        Abc_NtkDelete( pNtkRes );
        Abc_Print( -1, "pa_strash: could not assign coordinates to every AIG node.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: pa_strash [-h]\n" );
    Abc_Print( -2, "\t           strashes the network; after pa_place of a mapped network, every\n" );
    Abc_Print( -2, "\t           new AIG node inherits the center of the cell that produced it\n" );
    Abc_Print( -2, "\t-h       : print the command usage\n" );
    Abc_Print( -2, "\t           \n" );
    Abc_Print( -2, "\t           For example, command line \"&get; &nf; &put; pa_place; pa_strash; pa_rw -c\"\n" );
    Pa_PrintAcknowledgment();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Registers the commands of the package.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_place",  Pa_CommandPlace,        0 );
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_stats",  Pa_CommandStats,        0 );
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_rs",     Pa_CommandResubstitute, 1 );
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_rw",     Pa_CommandRewrite,      1 );
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_rf",     Pa_CommandRefactor,     1 );
    Cmd_CommandAdd( pAbc, "Physical synthesis", "pa_strash", Pa_CommandStrash,       1 );
}

/**Function*************************************************************

  Synopsis    [Returns one slot of the state of the current frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Pa_FrameState( int Slot, void * (*pAlloc)( void ), void (*pFree)( void * ) )
{
    Abc_Frame_t * pAbc = Abc_FrameGetGlobalFrame();
    Pa_Man_t * p = (Pa_Man_t *)pAbc->pAbcPa;
    if ( p == NULL )
        pAbc->pAbcPa = p = ABC_CALLOC( Pa_Man_t, 1 );
    if ( p->pState[Slot] == NULL )
    {
        p->pState[Slot] = pAlloc();
        p->pFree[Slot]  = pFree;
    }
    return p->pState[Slot];
}

/**Function*************************************************************

  Synopsis    [Frees the state of the package kept in the frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_End( Abc_Frame_t * pAbc )
{
    Pa_Man_t * p = (Pa_Man_t *)pAbc->pAbcPa;
    int i;
    if ( p == NULL )
        return;
    for ( i = 0; i < PA_STATE_NUM; i++ )
        if ( p->pState[i] )
            p->pFree[i]( p->pState[i] );
    ABC_FREE( p );
    pAbc->pAbcPa = NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
