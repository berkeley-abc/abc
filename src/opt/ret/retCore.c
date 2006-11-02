/**CFile****************************************************************

  FileName    [retCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    [The core retiming procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retCore.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implementation of retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetime( Abc_Ntk_t * pNtk, int Mode, int fVerbose )
{
    int RetValue;
    assert( Mode > 0 && Mode < 6 );
    // perform forward retiming
    switch ( Mode )
    {
    case 1: // forward 
        RetValue = Abc_NtkRetimeForward( pNtk, fVerbose );
        break;
    case 2: // backward 
        RetValue = Abc_NtkRetimeBackward( pNtk, fVerbose );
        break;
    case 3: // min-area 
        RetValue = Abc_NtkRetimeMinArea( pNtk, fVerbose );
        break;
    case 4: // min-delay
        RetValue = Abc_NtkRetimeMinDelay( pNtk, fVerbose );
        break;
    case 5: // min-area + min-delay
        RetValue  = Abc_NtkRetimeMinArea( pNtk, fVerbose );
        RetValue += Abc_NtkRetimeMinDelay( pNtk, fVerbose );
        break;
    default:
        printf( "Unknown retiming option.\n" );
        break;
    }
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


