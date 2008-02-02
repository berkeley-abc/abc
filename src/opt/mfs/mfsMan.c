/**CFile****************************************************************

  FileName    [mfsMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedure to manipulation the manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"

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
Mfs_Man_t * Mfs_ManAlloc()
{
    Mfs_Man_t * p;
    // start the manager
    p = ALLOC( Mfs_Man_t, 1 );
    memset( p, 0, sizeof(Mfs_Man_t) );
    p->vProjVars = Vec_IntAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfs_ManClean( Mfs_Man_t * p )
{
    if ( p->pAigWin )
        Aig_ManStop( p->pAigWin );
    if ( p->pCnf )
        Cnf_DataFree( p->pCnf );
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    if ( p->vRoots )
        Vec_PtrFree( p->vRoots );
    if ( p->vSupp )
        Vec_PtrFree( p->vSupp );
    if ( p->vNodes )
        Vec_PtrFree( p->vNodes );
    p->pAigWin = NULL;
    p->pCnf = NULL;
    p->pSat = NULL;
    p->vRoots = NULL;
    p->vSupp = NULL;
    p->vNodes = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfs_ManPrint( Mfs_Man_t * p )
{
    printf( "Nodes tried = %d. Bad nodes = %d.\n", 
        p->nNodesTried, p->nNodesBad );
    printf( "Total mints = %d. Care mints = %d. Ratio = %5.2f.\n", 
        p->nMintsTotal, p->nMintsCare, 1.0 * p->nMintsCare / p->nMintsTotal );
    PRT( "Win", p->timeWin );
    PRT( "Aig", p->timeAig );
    PRT( "Cnf", p->timeCnf );
    PRT( "Sat", p->timeSat );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfs_ManStop( Mfs_Man_t * p )
{
    Mfs_ManPrint( p );
    Mfs_ManClean( p );
    Vec_IntFree( p->vProjVars );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


