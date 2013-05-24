/**CFile****************************************************************

  FileName    [sfmCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

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
void Sfm_ParSetDefault( Sfm_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Sfm_Par_t) );
    pPars->nTfoLevMax   =    2;  // the maximum fanout levels
    pPars->nFanoutMax   =   10;  // the maximum number of fanouts
    pPars->nDepthMax    =    0;  // the maximum depth to try
    pPars->nWinSizeMax  =  500;  // the maximum number of divisors
    pPars->nBTLimit     =    0;  // the maximum number of conflicts in one SAT run
    pPars->fFixLevel    =    0;  // does not allow level to increase
    pPars->fArea        =    0;  // performs optimization for area
    pPars->fMoreEffort  =    0;  // performs high-affort minimization
    pPars->fVerbose     =    0;  // enable basic stats
    pPars->fVeryVerbose =    0;  // enable detailed stats
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkPrepare( Sfm_Ntk_t * p )
{
    p->vLeaves = Vec_IntAlloc( 1000 );
    p->vRoots  = Vec_IntAlloc( 1000 );
    p->vNodes  = Vec_IntAlloc( 1000 );
    p->vTfo    = Vec_IntAlloc( 1000 );
    p->vDivs   = Vec_IntAlloc( 100 );
    p->vDivIds = Vec_IntAlloc( 1000 );
    p->vDiffs  = Vec_IntAlloc( 1000 );
    p->vLits   = Vec_IntAlloc( 100 );
    p->vClauses  = Vec_WecAlloc( 100 );
    p->vFaninMap = Vec_IntAlloc( 10 );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NtkPerform( Sfm_Ntk_t * p, Sfm_Par_t * pPars )
{
//    int i;
    p->pPars = pPars;
    Sfm_NtkPrepare( p );
    Sfm_ComputeInterpolantCheck( p );
/*
    Sfm_NtkForEachNode( p, i )
    {
//        printf( "Node %d:\n", i );
//        Sfm_PrintCnf( (Vec_Str_t *)Vec_WecEntry(p->vCnfs, i) );
//        printf( "\n" );
        Sfm_NtkWindow( p, i, 1 );
    }
*/
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

