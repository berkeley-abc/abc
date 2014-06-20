/**CFile****************************************************************

  FileName    [giaGig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Parser for Gate-Inverter Graph by Niklas Een.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaGig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef enum { 
    GIG_NONE   =  0,
    GIG_RESET  =  1,
    GIG_PI     =  2,
    GIG_PO     =  3,
    GIG_SEQ    =  4,
    GIG_LUT    =  5,
    GIG_DELAY  =  6,
    GIG_BOX    =  7,
    GIG_SEL    =  8,
    GIG_BAR    =  9,
    GIG_UNUSED = 10     
};

static char * s_GigNames[GIG_UNUSED] = 
{
    "NONE",   // GIG_NONE   = 0
    "Reset",  // GIG_RESET  = 1
    "PI",     // GIG_PI     = 2
    "PO",     // GIG_PO     = 3
    "Seq",    // GIG_SEQ    = 4
    "Lut4",   // GIG_LUT    = 5
    "Delay",  // GIG_DELAY  = 6
    "Box",    // GIG_BOX    = 7
    "Sel",    // GIG_SEL    = 8
    "Bar"     // GIG_BAR    = 9
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManBuildGig( Vec_Int_t * vObjs, Vec_Int_t * vStore )
{
    int i, Type, nObjs[GIG_UNUSED] = {0};
    printf( "Parsed %d objects and %d tokens.\n", Vec_IntSize(vObjs), Vec_IntSize(vStore) );
    for ( i = 0; i < Vec_IntSize(vObjs); i++ )
    {
        Type = Vec_IntEntry( vStore, Vec_IntEntry(vObjs,i) + 1 );
        nObjs[Type]++;
    }
    printf( "Statistics:  " );
    for ( i = 1; i < GIG_UNUSED; i++ )
        printf( "%s = %d   ", s_GigNames[i], nObjs[i] );
    printf( "\n" );
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManReadGig( char * pFileName )
{
    Gia_Man_t * pNew;
    int Type, Offset, fEndOfLine, Digit, nObjs; 
    char * pChars  = " w(-,)]\r\t";
    char * pBuffer = Extra_FileReadContents( pFileName );
    char * pStart  = pBuffer, * pToken;
    Vec_Int_t * vObjs, * vStore;
    if ( pBuffer == NULL )
        printf( "Cannot open input file %s\n", pFileName );
    // count objects
    for ( nObjs = 0, pToken = pBuffer; *pToken; pToken++ )
        nObjs += (int)(*pToken == '\n');
    // read objects
    vObjs  = Vec_IntAlloc( nObjs );
    vStore = Vec_IntAlloc( 10*nObjs );
    while ( 1 )
    {
        // read net ID
        pToken = strtok( pStart, pChars );
        pStart = NULL;
        if ( pToken == NULL )
            break;
        // start new object
        Vec_IntPush( vObjs, Vec_IntSize(vStore) );
        // save net ID
        assert( pToken[0] >= '0' && pToken[0] <= '9' );
        Vec_IntPush( vStore, atoi(pToken) );
        // read equal
        pToken = strtok( pStart, pChars );
        assert( pToken[0] == '=' );
        // read type
        pToken = strtok( pStart, pChars );
        fEndOfLine = 0;
        if ( pToken[strlen(pToken)-1] == '\n' )
        {
            pToken[strlen(pToken)-1] = 0;
            fEndOfLine = 1;
        }
        for ( Type = GIG_RESET; Type < GIG_UNUSED; Type++ )
            if ( !strcmp(pToken, s_GigNames[Type]) )
                break;
        assert( Type < GIG_UNUSED );
        Vec_IntPush( vStore, Type );
        if ( fEndOfLine )
            continue;
        // read fanins
        Offset = Vec_IntSize(vStore);
        Vec_IntPush( vStore, 0 );
        while ( 1 )
        {
            pToken = strtok( pStart, pChars );
            if ( pToken == NULL || pToken[0] == '\n' || pToken[0] == '[' )
                break;
            assert( pToken[0] >= '0' && pToken[0] <= '9' );
            Vec_IntPush( vStore, atoi(pToken) );
            Vec_IntAddToEntry( vStore, Offset, 1 );
        }
        assert( pToken != NULL );
        if ( pToken[0] == '\n' )
            continue;
        assert( pToken[0] == '[' );
        // read attribute
        pToken++;
        if ( Type == GIG_LUT )
        {
            assert( strlen(pToken) == 4 );
            Digit  = Abc_TtReadHexDigit(pToken[0]);
            Digit |= Abc_TtReadHexDigit(pToken[1]) << 4;
            Digit |= Abc_TtReadHexDigit(pToken[2]) << 8;
            Digit |= Abc_TtReadHexDigit(pToken[3]) << 12;
            Vec_IntPush( vStore, Digit );
        }
        else
        {
            assert( Type == GIG_DELAY );
            Vec_IntPush( vStore, atoi(pToken) );
        }
        // read end of line
        pToken = strtok( pStart, pChars );
        assert( pToken[0] == '\n' );
    }
    ABC_FREE( pBuffer );
    // create AIG
    pNew = Gia_ManBuildGig( vObjs, vStore );
    // cleanup
    Vec_IntFree( vObjs );
    Vec_IntFree( vStore );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

