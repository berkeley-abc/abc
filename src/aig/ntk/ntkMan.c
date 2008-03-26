/**CFile****************************************************************

  FileName    [ntkMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Network manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Man_t * Ntk_ManAlloc()
{
    Ntk_Man_t * p;
    p = ALLOC( Ntk_Man_t, 1 );
    memset( p, 0, sizeof(Ntk_Man_t) );
    p->vCis = Vec_PtrAlloc( 1000 );
    p->vCos = Vec_PtrAlloc( 1000 );
    p->vObjs = Vec_PtrAlloc( 1000 );
    p->vTemp = Vec_PtrAlloc( 1000 );
    p->nFanioPlus = 4;
    p->pMemObjs = Aig_MmFlexStart();
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManFree( Ntk_Man_t * p )
{
    if ( p->pName )    free( p->pName );
    if ( p->pSpec )    free( p->pSpec );
    if ( p->vCis )     Vec_PtrFree( p->vCis );
    if ( p->vCos )     Vec_PtrFree( p->vCos );
    if ( p->vObjs )    Vec_PtrFree( p->vObjs );
    if ( p->vTemp )    Vec_PtrFree( p->vTemp );
    if ( p->pAig )     Aig_ManStop( p->pAig );
    if ( p->pManTime ) Tim_ManStop( p->pManTime );
    if ( p->pMemObjs ) Aig_MmFlexStop( p->pMemObjs, 0 );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Deallocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManPrintStats( Ntk_Man_t * p )
{
    printf( "%-15s : ",      p->pName );
    printf( "pi = %5d  ",    Ntk_ManPiNum(p) );
    printf( "po = %5d  ",    Ntk_ManPoNum(p) );
    printf( "ci = %5d  ",    Ntk_ManCiNum(p) );
    printf( "co = %5d  ",    Ntk_ManCoNum(p) );
    printf( "lat = %5d  ",   Ntk_ManLatchNum(p) );
    printf( "box = %5d  ",   Ntk_ManBoxNum(p) );
    printf( "node = %5d  ",  Ntk_ManNodeNum(p) );
    printf( "aig = %6d  ",   Aig_ManNodeNum(p->pAig) );
    printf( "\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


