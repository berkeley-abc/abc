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

  Synopsis    [Cleanups extended representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManCleanup( Ntl_Man_t * p )
{
    Vec_PtrClear( p->vCis );
    Vec_PtrClear( p->vCos );
    Vec_PtrClear( p->vNodes );
    Vec_IntClear( p->vBox1Cos );
    if ( p->pAig )
    {
        Aig_ManStop( p->pAig );
        p->pAig = NULL;
    }
    if ( p->pManTime )
    {
        Tim_ManStop( p->pManTime );
        p->pManTime = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Duplicates the design without the nodes of the root model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManStartFrom( Ntl_Man_t * pOld )
{
    Ntl_Man_t * pNew;
    Ntl_Mod_t * pModel;
    Ntl_Obj_t * pBox;
    Ntl_Net_t * pNet;
    int i, k;
    pNew = Ntl_ManAlloc( pOld->pSpec );
    Vec_PtrForEachEntry( pOld->vModels, pModel, i )
        if ( i == 0 )
        {
            Ntl_ManMarkCiCoNets( pOld );
            pModel->pCopy = Ntl_ModelStartFrom( pNew, pModel );
            Ntl_ManUnmarkCiCoNets( pOld );
        }
        else
            pModel->pCopy = Ntl_ModelDup( pNew, pModel );
    Vec_PtrForEachEntry( pOld->vModels, pModel, i )
        Ntl_ModelForEachBox( pModel, pBox, k )
            ((Ntl_Obj_t *)pBox->pCopy)->pImplem = pBox->pImplem->pCopy;
    Ntl_ManForEachCiNet( pOld, pNet, i )
        Vec_PtrPush( pNew->vCis, pNet->pCopy );
    Ntl_ManForEachCoNet( pOld, pNet, i )
        Vec_PtrPush( pNew->vCos, pNet->pCopy );
    if ( pOld->pManTime )
        pNew->pManTime = Tim_ManDup( pOld->pManTime, 0 );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the design.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManDup( Ntl_Man_t * pOld )
{
    Ntl_Man_t * pNew;
    Ntl_Mod_t * pModel;
    Ntl_Obj_t * pBox;
    Ntl_Net_t * pNet;
    int i, k;
    pNew = Ntl_ManAlloc( pOld->pSpec );
    Vec_PtrForEachEntry( pOld->vModels, pModel, i )
        pModel->pCopy = Ntl_ModelDup( pNew, pModel );
    Vec_PtrForEachEntry( pOld->vModels, pModel, i )
        Ntl_ModelForEachBox( pModel, pBox, k )
            ((Ntl_Obj_t *)pBox->pCopy)->pImplem = pBox->pImplem->pCopy;
    Ntl_ManForEachCiNet( pOld, pNet, i )
        Vec_PtrPush( pNew->vCis, pNet->pCopy );
    Ntl_ManForEachCoNet( pOld, pNet, i )
        Vec_PtrPush( pNew->vCos, pNet->pCopy );
    if ( pOld->pManTime )
        pNew->pManTime = Tim_ManDup( pOld->pManTime, 0 );
    if ( !Ntl_ManCheck( pNew ) )
        printf( "Ntl_ManDup: The check has failed for design %s.\n", pNew->pName );
    return pNew;
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

  Synopsis    [Returns 1 if the design is combinational.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManIsComb( Ntl_Man_t * p )          
{ 
    return Ntl_ModelLatchNum(Ntl_ManRootModel(p)) == 0; 
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
    pRoot = Ntl_ManRootModel( p );
    printf( "%-15s : ",        p->pName );
    printf( "pi = %5d  ",      Ntl_ModelPiNum(pRoot) );
    printf( "po = %5d  ",      Ntl_ModelPoNum(pRoot) );
    printf( "lat = %5d  ",     Ntl_ModelLatchNum(pRoot) );
    printf( "node = %5d  ",    Ntl_ModelNodeNum(pRoot) );
    printf( "inv/buf = %5d  ", Ntl_ModelLut1Num(pRoot) );
    printf( "box = %4d  ",     Ntl_ModelBoxNum(pRoot) );
    printf( "mod = %3d  ",     Vec_PtrSize(p->vModels) );
    printf( "net = %d",       Ntl_ModelCountNets(pRoot) );
    printf( "\n" );
    fflush( stdout );
    assert( Ntl_ModelLut1Num(pRoot) == Ntl_ModelCountLut1(pRoot) );
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
    p->vObjs = Vec_PtrAlloc( 1000 );
    p->vPis  = Vec_PtrAlloc( 100 );
    p->vPos  = Vec_PtrAlloc( 100 );
    // start the table
    p->nTableSize = Aig_PrimeCudd( 1000 );
    p->pTable = ALLOC( Ntl_Net_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Ntl_Net_t *) * p->nTableSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the model without nodes but with CI/CO nets.]

  Description [The CI/CO nets of the old model should be marked before 
  calling this procedure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ModelStartFrom( Ntl_Man_t * pManNew, Ntl_Mod_t * pModelOld )
{
    Ntl_Mod_t * pModelNew;
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i, k;
    pModelNew = Ntl_ModelAlloc( pManNew, pModelOld->pName );
    Ntl_ModelForEachObj( pModelOld, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
            pObj->pCopy = NULL;
        else
            pObj->pCopy = Ntl_ModelDupObj( pModelNew, pObj );
    }
    Ntl_ModelForEachNet( pModelOld, pNet, i )
    {
        if ( pNet->fMark )
        {
            pNet->pCopy = Ntl_ModelFindOrCreateNet( pModelNew, pNet->pName );
            ((Ntl_Net_t *)pNet->pCopy)->pDriver = pNet->pDriver->pCopy;
        }
        else
            pNet->pCopy = NULL;
    }
    Ntl_ModelForEachObj( pModelOld, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
            continue;
        Ntl_ObjForEachFanin( pObj, pNet, k )
            if ( pNet->pCopy != NULL )
                Ntl_ObjSetFanin( pObj->pCopy, pNet->pCopy, k );
        Ntl_ObjForEachFanout( pObj, pNet, k )
            if ( pNet->pCopy != NULL )
                Ntl_ObjSetFanout( pObj->pCopy, pNet->pCopy, k );
        if ( Ntl_ObjIsLatch(pObj) )
            ((Ntl_Obj_t *)pObj->pCopy)->LatchId = pObj->LatchId;
    }
    pModelNew->vDelays = pModelOld->vDelays? Vec_IntDup( pModelOld->vDelays ) : NULL;
    pModelNew->vArrivals = pModelOld->vArrivals? Vec_IntDup( pModelOld->vArrivals ) : NULL;
    pModelNew->vRequireds = pModelOld->vRequireds? Vec_IntDup( pModelOld->vRequireds ) : NULL;
    return pModelNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ModelDup( Ntl_Man_t * pManNew, Ntl_Mod_t * pModelOld )
{
    Ntl_Mod_t * pModelNew;
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i, k;
    pModelNew = Ntl_ModelAlloc( pManNew, pModelOld->pName );
    Ntl_ModelForEachObj( pModelOld, pObj, i )
        pObj->pCopy = Ntl_ModelDupObj( pModelNew, pObj );
    Ntl_ModelForEachNet( pModelOld, pNet, i )
    {
        pNet->pCopy = Ntl_ModelFindOrCreateNet( pModelNew, pNet->pName );
        ((Ntl_Net_t *)pNet->pCopy)->pDriver = pNet->pDriver->pCopy;
        assert( pNet->pDriver->pCopy != NULL );
    }
    Ntl_ModelForEachObj( pModelOld, pObj, i )
    {
        Ntl_ObjForEachFanin( pObj, pNet, k )
            Ntl_ObjSetFanin( pObj->pCopy, pNet->pCopy, k );
        Ntl_ObjForEachFanout( pObj, pNet, k )
            Ntl_ObjSetFanout( pObj->pCopy, pNet->pCopy, k );
        if ( Ntl_ObjIsLatch(pObj) )
            ((Ntl_Obj_t *)pObj->pCopy)->LatchId = pObj->LatchId;
        if ( Ntl_ObjIsNode(pObj) )
            ((Ntl_Obj_t *)pObj->pCopy)->pSop = Ntl_ManStoreSop( pManNew->pMemSops, pObj->pSop );
    }
    pModelNew->vDelays = pModelOld->vDelays? Vec_IntDup( pModelOld->vDelays ) : NULL;
    pModelNew->vArrivals = pModelOld->vArrivals? Vec_IntDup( pModelOld->vArrivals ) : NULL;
    pModelNew->vRequireds = pModelOld->vRequireds? Vec_IntDup( pModelOld->vRequireds ) : NULL;
    return pModelNew;
}

/**Function*************************************************************

  Synopsis    [Deallocates the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelFree( Ntl_Mod_t * p )
{
    assert( Ntl_ManCheckNetsAreNotMarked(p) );
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


