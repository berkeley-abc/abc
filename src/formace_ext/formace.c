/**CFile****************************************************************

  FileName    [formace.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE extension commands.]

  Synopsis    [Experimental extension commands for ForMACE work.]

***********************************************************************/

#include "base/main/mainInt.h"
#include "base/cmd/cmd.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void ForMace_Init( Abc_Frame_t * pAbc );
static void ForMace_End( Abc_Frame_t * pAbc );
static int  ForMace_CommandSummary( Abc_Frame_t * pAbc, int argc, char ** argv );

static Abc_FrameInitializer_t ForMace_FrameInitializer = { ForMace_Init, ForMace_End, NULL, NULL };

#if defined(__GNUC__)
static void ForMace_Register( void ) __attribute__((constructor));
static void ForMace_Register( void )
{
    Abc_FrameAddInitializer( &ForMace_FrameInitializer );
}
#else
#error "ForMACE extension registration currently requires a compiler with constructor attributes."
#endif

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void ForMace_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "ForMACE", "fm_summary", ForMace_CommandSummary, 0 );
}

static void ForMace_End( Abc_Frame_t * pAbc )
{
}

static int ForMace_CommandSummary( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose = 0;

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

    if ( argc != globalUtilOptind )
        goto usage;

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "There is no current network.\n" );
        return 1;
    }

    fprintf( pAbc->Out, "ForMACE summary for \"%s\":\n", Abc_NtkName(pNtk) );
    fprintf( pAbc->Out, "  pi      = %d\n", Abc_NtkPiNum(pNtk) );
    fprintf( pAbc->Out, "  po      = %d\n", Abc_NtkPoNum(pNtk) );
    fprintf( pAbc->Out, "  latches = %d\n", Abc_NtkLatchNum(pNtk) );
    fprintf( pAbc->Out, "  nodes   = %d\n", Abc_NtkNodeNum(pNtk) );
    fprintf( pAbc->Out, "  levels  = %d\n", Abc_NtkLevel(pNtk) );

    if ( fVerbose )
    {
        fprintf( pAbc->Out, "  objects = %d\n", Abc_NtkObjNum(pNtk) );
        fprintf( pAbc->Out, "  type    = %s\n", Abc_NtkIsStrash(pNtk) ? "strashed AIG" : "logic network" );
        fprintf( pAbc->Out, "  seq     = %s\n", Abc_NtkIsComb(pNtk) ? "combinational" : "sequential" );
    }

    return 0;

usage:
    fprintf( pAbc->Err, "usage: fm_summary [-vh]\n" );
    fprintf( pAbc->Err, "\t-v    : toggle verbose network details [default = %s]\n", fVerbose ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-h    : print the command usage\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
