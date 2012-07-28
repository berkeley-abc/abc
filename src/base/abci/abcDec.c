/**CFile****************************************************************

  FileName    [abcDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures for testing and comparing decomposition algorithms.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
// decomposition type
// 0 - none
// 1 - factoring
// 2 - bi-decomposition
// 3 - DSD

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Testbench for decomposition algorithms.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_DecTest( char * pFileName, int DecType )
{
    printf( "Trying to read file \"%s\".\n", pFileName );
    fflush( stdout );
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

