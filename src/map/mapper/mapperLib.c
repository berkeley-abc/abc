/**CFile****************************************************************

  FileName    [mapperLib.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [Generic technology mapping engine.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 2.0. Started - June 1, 2004.]

  Revision    [$Id: mapperLib.c,v 1.6 2005/01/23 06:59:44 alanmi Exp $]

***********************************************************************/
#define _BSD_SOURCE

#ifndef WIN32
#include <unistd.h>
#endif

#include "mapperInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads in the supergate library and prepares it for use.]

  Description [The supergates library comes in a .super file. This file
  contains descriptions of supergates along with some relevant information.
  This procedure reads the supergate file, canonicizes the supergates,
  and constructs an additional lookup table, which can be used to map
  truth tables of the cuts into the pair (phase, supergate). The phase
  indicates how the current truth table should be phase assigned to 
  match the canonical form of the supergate. The resulting phase is the
  bitwise EXOR of the phase needed to canonicize the supergate and the
  phase needed to transform the truth table into its canonical form.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Map_SuperLib_t * Map_SuperLibCreate( char * pFileName, char * pExcludeFile, int fAlgorithm, int fVerbose )
{
    Map_SuperLib_t * p;
    clock_t clk;

    // start the supergate library
    p = ABC_ALLOC( Map_SuperLib_t, 1 );
    memset( p, 0, sizeof(Map_SuperLib_t) );
    p->pName     = pFileName;
    p->fVerbose  = fVerbose;
    p->mmSupers  = Extra_MmFixedStart( sizeof(Map_Super_t) );
    p->mmEntries = Extra_MmFixedStart( sizeof(Map_HashEntry_t) );
    p->mmForms   = Extra_MmFlexStart();
    Map_MappingSetupTruthTables( p->uTruths );

    // start the hash table
    p->tTableC = Map_SuperTableCreate( p );
    p->tTable  = Map_SuperTableCreate( p );

    // read the supergate library from file
clk = clock();
    if ( fAlgorithm )
    {
        if ( !Map_LibraryReadTree( p, pFileName, pExcludeFile ) )
        {
            Map_SuperLibFree( p );
            return NULL;
        }
    }
    else
    {
        if ( pExcludeFile != 0 )
        {
            Map_SuperLibFree( p );
            printf ("Error: Exclude file support not present for old format. Stop.\n");
            return NULL;
        }
        if ( !Map_LibraryRead( p, pFileName ) )
        {
            Map_SuperLibFree( p );
            return NULL;
        }
    }
    assert( p->nVarsMax > 0 );

    // report the stats
if ( fVerbose ) {
    printf( "Loaded %d unique %d-input supergates from \"%s\".  ", 
        p->nSupersReal, p->nVarsMax, pFileName );
    ABC_PRT( "Time", clock() - clk );
}

    // assign the interver parameters
    p->pGateInv        = Mio_LibraryReadInv( p->pGenlib );
    p->tDelayInv.Rise  = Mio_LibraryReadDelayInvRise( p->pGenlib );
    p->tDelayInv.Fall  = Mio_LibraryReadDelayInvFall( p->pGenlib );
    p->tDelayInv.Worst = MAP_MAX( p->tDelayInv.Rise, p->tDelayInv.Fall );
    p->AreaInv         = Mio_LibraryReadAreaInv( p->pGenlib );
    p->AreaBuf         = Mio_LibraryReadAreaBuf( p->pGenlib );

    // assign the interver supergate
    p->pSuperInv = (Map_Super_t *)Extra_MmFixedEntryFetch( p->mmSupers );
    memset( p->pSuperInv, 0, sizeof(Map_Super_t) );
    p->pSuperInv->Num         = -1;
    p->pSuperInv->nGates      =  1;
    p->pSuperInv->nFanins     =  1;
    p->pSuperInv->nFanLimit   = 10;
    p->pSuperInv->pFanins[0]  = p->ppSupers[0];
    p->pSuperInv->pRoot       = p->pGateInv;
    p->pSuperInv->Area        = p->AreaInv;
    p->pSuperInv->tDelayMax   = p->tDelayInv;
    p->pSuperInv->tDelaysR[0].Rise = MAP_NO_VAR;
    p->pSuperInv->tDelaysR[0].Fall = p->tDelayInv.Rise;
    p->pSuperInv->tDelaysF[0].Rise = p->tDelayInv.Fall;
    p->pSuperInv->tDelaysF[0].Fall = MAP_NO_VAR;
    return p;
}


/**Function*************************************************************

  Synopsis    [Deallocates the supergate library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_SuperLibFree( Map_SuperLib_t * p )
{
    if ( p == NULL ) return;
    if ( p->pGenlib )
    {
        assert( p->pGenlib == Abc_FrameReadLibGen() );
        Mio_LibraryDelete( p->pGenlib );
        Abc_FrameSetLibGen( NULL );
    }
    if ( p->tTableC )
        Map_SuperTableFree( p->tTableC );
    if ( p->tTable )
        Map_SuperTableFree( p->tTable );
    Extra_MmFixedStop( p->mmSupers );
    Extra_MmFixedStop( p->mmEntries );
    Extra_MmFlexStop( p->mmForms );
    ABC_FREE( p->ppSupers );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Derives the library from the genlib library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Map_SuperLibDeriveFromGenlib( Mio_Library_t * pLib )
{
    Abc_Frame_t * pAbc = Abc_FrameGetGlobalFrame();
    char * pNameGeneric;
    char * FileNameGenlib;
    char * FileNameSuper;
    char * CommandSuper;
    char * CommandRead;
    FILE * pFile;

    if ( pLib == NULL )
        return 0;

    FileNameGenlib = ABC_ALLOC( char, 10000 );
    FileNameSuper = ABC_ALLOC( char, 10000 );
    CommandSuper = ABC_ALLOC( char, 10000 );
    CommandRead = ABC_ALLOC( char, 10000 );

    // write the current library into the file
    sprintf( FileNameGenlib, "%s_temp", Mio_LibraryReadName(pLib) );
    pFile = fopen( FileNameGenlib, "w" );
    Mio_WriteLibrary( pFile, pLib, 0 );
    fclose( pFile );

    // get the file name with the library
    pNameGeneric = Extra_FileNameGeneric( Mio_LibraryReadName(pLib) );
    sprintf( FileNameSuper, "%s.super", pNameGeneric );
    ABC_FREE( pNameGeneric );
 
    sprintf( CommandSuper,  "super -L 1 -I 5 -D 10000000 -A 10000000 -T 100 %s", FileNameGenlib ); 
    if ( Cmd_CommandExecute( pAbc, CommandSuper ) )
    {
        ABC_FREE( FileNameGenlib );
        ABC_FREE( FileNameSuper );
        ABC_FREE( CommandSuper );
        ABC_FREE( CommandRead );
        fprintf( stdout, "Cannot execute command \"%s\".\n", CommandSuper );
        return 0;
    }
//#ifdef WIN32
//        _unlink( FileNameGenlib );
//#else
//        unlink( FileNameGenlib );
//#endif
    printf( "A simple supergate library is derived from gate library \"%s\".\n", Mio_LibraryReadName(pLib) );
    fflush( stdout );

    sprintf( CommandRead,  "read_super %s", FileNameSuper ); 
    if ( Cmd_CommandExecute( pAbc, CommandRead ) )
    {
//#ifdef WIN32
//        _unlink( FileNameSuper );
//#else
//       unlink( FileNameSuper );
//#endif
        fprintf( stdout, "Cannot execute command \"%s\".\n", CommandRead );
        ABC_FREE( FileNameGenlib );
        ABC_FREE( FileNameSuper );
        ABC_FREE( CommandSuper );
        ABC_FREE( CommandRead );
        return 0;
    }
//#ifdef WIN32
//    _unlink( FileNameSuper );
//#else
//    unlink( FileNameSuper );
//#endif
    ABC_FREE( FileNameGenlib );
    ABC_FREE( FileNameSuper );
    ABC_FREE( CommandSuper );
    ABC_FREE( CommandRead );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

