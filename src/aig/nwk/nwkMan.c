/**CFile****************************************************************

  FileName    [nwkMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Logic network representation.]
 
  Synopsis    [Network manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Nwk_ManAlloc()
{
    Nwk_Man_t * p;
    p = ALLOC( Nwk_Man_t, 1 );
    memset( p, 0, sizeof(Nwk_Man_t) );
    p->vCis = Vec_PtrAlloc( 1000 );
    p->vCos = Vec_PtrAlloc( 1000 );
    p->vObjs = Vec_PtrAlloc( 1000 );
    p->vTemp = Vec_PtrAlloc( 1000 );
    p->nFanioPlus = 2;
    p->pMemObjs = Aig_MmFlexStart();
    p->pManHop = Hop_ManStart();
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManFree( Nwk_Man_t * p )
{
//    printf( "The number of realloced nodes = %d.\n", p->nRealloced );
    if ( p->pName )    free( p->pName );
    if ( p->pSpec )    free( p->pSpec );
    if ( p->vCis )     Vec_PtrFree( p->vCis );
    if ( p->vCos )     Vec_PtrFree( p->vCos );
    if ( p->vObjs )    Vec_PtrFree( p->vObjs );
    if ( p->vTemp )    Vec_PtrFree( p->vTemp );
    if ( p->pManTime ) Tim_ManStop( p->pManTime );
    if ( p->pMemObjs ) Aig_MmFlexStop( p->pMemObjs, 0 );
    if ( p->pManHop )  Hop_ManStop( p->pManHop );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManPrintStats( Nwk_Man_t * p, If_Lib_t * pLutLib )
{
    p->pLutLib = pLutLib;
    printf( "%-15s : ",      p->pName );
    printf( "pi = %5d  ",    Nwk_ManPiNum(p) );
    printf( "po = %5d  ",    Nwk_ManPoNum(p) );
    printf( "ci = %5d  ",    Nwk_ManCiNum(p) );
    printf( "co = %5d  ",    Nwk_ManCoNum(p) );
    printf( "lat = %5d  ",   Nwk_ManLatchNum(p) );
    printf( "node = %5d  ",  Nwk_ManNodeNum(p) );
    printf( "aig = %6d  ",   Nwk_ManGetAigNodeNum(p) );
    printf( "lev = %3d  ",   Nwk_ManLevel(p) );
//    printf( "lev2 = %3d  ",  Nwk_ManLevelBackup(p) );
    printf( "delay = %5.2f", Nwk_ManDelayTraceLut(p) );
    printf( "\n" );
//    Nwk_ManDelayTracePrint( p, pLutLib );
    fflush( stdout );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


