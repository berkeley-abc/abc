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
    int c, fUseMogs = 1, fAreaMode = 0, fVerbose = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "amvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAreaMode ^= 1;
            break;
        case 'm':
            fUseMogs ^= 1;
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

    if ( fVerbose )
    {
        int nMogPairs = fUseMogs ? Emap_CommandCountMogPairs( pLib ) : 0;
        fprintf( pAbc->Out, "ABC-native emap setup: PI = %d  PO = %d  AND = %d\n",
            Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk), Abc_NtkNodeNum(pNtk) );
        fprintf( pAbc->Out, "GENLIB \"%s\": gates = %d  MOG pairs = %d  MOG use = %s  mode = %s\n",
            Mio_LibraryReadName(pLib), Mio_LibraryReadGateNum(pLib), nMogPairs, fUseMogs ? "yes" : "no", fAreaMode ? "area" : "delay" );
    }

    pNtkRes = Emap_ManMapAigStructural( pNtk, pLib, fUseMogs, fAreaMode, fVerbose );
    if ( pNtkRes == NULL )
    {
        fprintf( pAbc->Err, "ABC-native emap structural mapping has failed.\n" );
        return 1;
    }

    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: emap [-amvh]\n" );
    fprintf( pAbc->Err, "\t         maps the current AIG using the current GENLIB library\n" );
    fprintf( pAbc->Err, "\t-a     : toggle area-oriented mode without required-time pruning [default = %s]\n", fAreaMode ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-m     : toggle using multi-output gates when present [default = %s]\n", fUseMogs ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-v     : toggle verbose output [default = %s]\n", fVerbose ? "yes" : "no" );
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
