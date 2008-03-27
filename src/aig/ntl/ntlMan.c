/**CFile****************************************************************

  FileName    [ntlMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Netlist manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

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
Ntl_Man_t * Ntl_ManAlloc( char * pFileName )
{
    Ntl_Man_t * p;
    // start the manager
    p = ALLOC( Ntl_Man_t, 1 );
    memset( p, 0, sizeof(Ntl_Man_t) );
    p->vModels = Vec_PtrAlloc( 1000 );
    p->vCis = Vec_PtrAlloc( 1000 );
    p->vCos = Vec_PtrAlloc( 1000 );
    p->vNodes = Vec_PtrAlloc( 1000 );
    p->vBox1Cos = Vec_IntAlloc( 1000 );
    // start the manager
    p->pMemObjs = Aig_MmFlexStart();
    p->pMemSops = Aig_MmFlexStart();
    // same the names
    p->pName = Ntl_ManStoreFileName( p, pFileName );
    p->pSpec = Ntl_ManStoreName( p, pFileName );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManFree( Ntl_Man_t * p )
{
    if ( p->vModels )
    {
        Ntl_Mod_t * pModel;
        int i;
        Ntl_ManForEachModel( p, pModel, i )
            Ntl_ModelFree( pModel );
        Vec_PtrFree( p->vModels );
    }
    if ( p->vCis )     Vec_PtrFree( p->vCis );
    if ( p->vCos )     Vec_PtrFree( p->vCos );
    if ( p->vNodes )   Vec_PtrFree( p->vNodes );
    if ( p->vBox1Cos ) Vec_IntFree( p->vBox1Cos );
    if ( p->pMemObjs ) Aig_MmFlexStop( p->pMemObjs, 0 );
    if ( p->pMemSops ) Aig_MmFlexStop( p->pMemSops, 0 );
    if ( p->pAig )     Aig_ManStop( p->pAig );
    if ( p->pManTime ) Tim_ManStop( p->pManTime );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Find the model with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ManFindModel( Ntl_Man_t * p, char * pName )
{
    Ntl_Mod_t * pModel;
    int i;
    Vec_PtrForEachEntry( p->vModels, pModel, i )
        if ( !strcmp( pModel->pName, pName ) )
            return pModel;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Deallocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManPrintStats( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    pRoot = Vec_PtrEntry( p->vModels, 0 );
    printf( "%-15s : ",       p->pName );
    printf( "pi = %5d  ",    Ntl_ModelPiNum(pRoot) );
    printf( "po = %5d  ",    Ntl_ModelPoNum(pRoot) );
    printf( "latch = %5d  ", Ntl_ModelLatchNum(pRoot) );
    printf( "node = %5d  ",  Ntl_ModelNodeNum(pRoot) );
    printf( "box = %4d  ",   Ntl_ModelBoxNum(pRoot) );
    printf( "model = %3d",   Vec_PtrSize(p->vModels) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Deallocates the netlist manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Ntl_ManReadTimeMan( Ntl_Man_t * p )
{
    return p->pManTime;
}

/**Function*************************************************************

  Synopsis    [Allocates the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ModelAlloc( Ntl_Man_t * pMan, char * pName )
{
    Ntl_Mod_t * p;
    // start the manager
    p = ALLOC( Ntl_Mod_t, 1 );
    memset( p, 0, sizeof(Ntl_Mod_t) );
    p->pMan  = pMan;
    p->pName = Ntl_ManStoreName( p->pMan, pName );
    Vec_PtrPush( pMan->vModels, p );
    p->vObjs = Vec_PtrAlloc( 10000 );
    p->vPis  = Vec_PtrAlloc( 1000 );
    p->vPos  = Vec_PtrAlloc( 1000 );
    // start the table
    p->nTableSize = Aig_PrimeCudd( 10000 );
    p->pTable = ALLOC( Ntl_Net_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Ntl_Net_t *) * p->nTableSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelFree( Ntl_Mod_t * p )
{
    if ( p->vRequireds )  Vec_IntFree( p->vRequireds );
    if ( p->vArrivals )   Vec_IntFree( p->vArrivals );
    if ( p->vDelays )     Vec_IntFree( p->vDelays );
    Vec_PtrFree( p->vObjs );
    Vec_PtrFree( p->vPis );
    Vec_PtrFree( p->vPos );
    free( p->pTable );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


