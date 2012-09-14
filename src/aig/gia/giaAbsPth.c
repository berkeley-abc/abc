/**CFile****************************************************************

  FileName    [giaAbsPth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Interface to pthreads.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsPth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "gia.h"

// comment this out to disable pthreads
//#define ABC_USE_PTHREADS

#ifdef ABC_USE_PTHREADS

#ifdef WIN32
#include "../lib/pthread.h"
#else
#include <pthread.h>
#include <unistd.h>
#endif

#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start and stop proving abstracted model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#ifndef ABC_USE_PTHREADS

void Gia_Ga2ProveAbsracted( char * pFileName, int fVerbose ) {}
void Gia_Ga2ProveCancel( int fVerbose )                      {}
int  Gia_Ga2ProveCheck( int fVerbose )                       { return 0; }

#else // pthreads are used

void Gia_Ga2ProveAbsracted( char * pFileName, int fVerbose )
{
    Abc_Print( 1, "Trying to prove abstraction.\n" );
}
void Gia_Ga2ProveCancel( int fVerbose )
{
    Abc_Print( 1, "Canceling attempt to prove abstraction.\n" );
}
int Gia_Ga2ProveCheck( int fVerbose )
{
    return 0;
}

#endif


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

