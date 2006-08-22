/**CFile****************************************************************

  FileName    [abcLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Functions to manipulate verilog libraries.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLib.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Lib_t * Abc_LibCreate( char * pName )
{
    Abc_Lib_t * p;
    p = ALLOC( Abc_Lib_t, 1 );
    memset( p, 0, sizeof(Abc_Lib_t) );
    p->pName    = Extra_UtilStrsav( pName );
    p->tModules = st_init_table( strcmp, st_strhash );
    p->pManFunc = Aig_ManStart();
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LibFree( Abc_Lib_t * pLib )
{
    st_generator * gen;
    Abc_Ntk_t * pNtk;
    char * pName;
    if ( pLib->pName )
        free( pLib->pName );
    if ( pLib->pManFunc )
        Aig_ManStop( pLib->pManFunc );
    if ( pLib->tModules )
    {
        st_foreach_item( pLib->tModules, gen, (char**)&pName, (char**)&pNtk )
            Abc_NtkDelete( pNtk );
        st_free_table( pLib->tModules );
    }
    free( pLib );
}

/**Function*************************************************************

  Synopsis    [Frees the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_LibDeriveRoot( Abc_Lib_t * pLib )
{
    st_generator * gen;
    Abc_Ntk_t * pNtk;
    char * pName;
    if ( st_count(pLib->tModules) > 1 )
    {
        printf( "The design includes more than one module and is currently not used.\n" );
        return NULL;
    }
    // find the network
    st_foreach_item( pLib->tModules, gen, (char**)&pName, (char**)&pNtk )
    {
        st_free_gen(gen);
        break;
    }
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


