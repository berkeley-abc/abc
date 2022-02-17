/**CFile****************************************************************

  FileName    [wln.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Word-level network.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 23, 2018.]

  Revision    [$Id: wln.c,v 1.00 2018/09/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wln.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Wln_ReadGuidance( char * pFileName, Abc_Nam_t * p )
{
    char Buffer[1000] = {'\\'}, * pBuffer = Buffer+1;
    Vec_Int_t * vTokens = Vec_IntAlloc( 100 );
    FILE * pFile = fopen( pFileName, "rb" );
    while ( fscanf( pFile, "%s", pBuffer ) == 1 )
    {
        if ( pBuffer[(int)strlen(pBuffer)-1] == '\r' )
            pBuffer[(int)strlen(pBuffer)-1] = 0;
        if ( !strcmp(pBuffer, "prove") && Vec_IntSize(vTokens) % 4 == 3 ) // account for "property"
            Vec_IntPush( vTokens, -1 );
        if ( Vec_IntSize(vTokens) % 4 == 2 || Vec_IntSize(vTokens) % 4 == 3 )
            Vec_IntPush( vTokens, Abc_NamStrFindOrAdd(p, Buffer, NULL) );
        else
            Vec_IntPush( vTokens, Abc_NamStrFindOrAdd(p, pBuffer, NULL) );
    }
    fclose( pFile );
    if ( Vec_IntSize(vTokens) % 4 == 3 ) // account for "property"
        Vec_IntPush( vTokens, -1 );
    assert( Vec_IntSize(vTokens) % 4 == 0 );
    return vTokens;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

