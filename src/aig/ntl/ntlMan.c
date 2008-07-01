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
Ntl_Man_t * Ntl_ManAlloc()
{
    Ntl_Man_t * p;
    // start the manager
    p = ALLOC( Ntl_Man_t, 1 );
    memset( p, 0, sizeof(Ntl_Man_t) );
    p->vModels = Vec_PtrAlloc( 1000 );
    p->vCis = Vec_PtrAlloc( 1000 );
    p->vCos = Vec_PtrAlloc( 1000 );
    p->vVisNodes = Vec_PtrAlloc( 1000 );
    p->vBox1Cios = Vec_IntAlloc( 1000 );
    p->vRegClasses = Vec_IntAlloc( 1000 );
    // start the manager
    p->pMemObjs = Aig_MmFlexStart();
    p->pMemSops = Aig_MmFlexStart();
    // allocate model table
    p->nModTableSize = Aig_PrimeCudd( 100 );
    p->pModTable = ALLOC( Ntl_Mod_t *, p->nModTableSize );
    memset( p->pModTable, 0, sizeof(Ntl_Mod_t *) * p->nModTableSize );
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
    pNew = Ntl_ManAlloc();
    pNew->pName = Ntl_ManStoreFileName( pNew, pOld->pName );
    pNew->pSpec = Ntl_ManStoreName( pNew, pOld->pName );
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
    pNew = Ntl_ManAlloc();
    pNew->pName = Ntl_ManStoreFileName( pNew, pOld->pName );
    pNew->pSpec = Ntl_ManStoreName( pNew, pOld->pName );
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
    if ( p->vCis )       Vec_PtrFree( p->vCis );
    if ( p->vCos )       Vec_PtrFree( p->vCos );
    if ( p->vVisNodes )  Vec_PtrFree( p->vVisNodes );
    if ( p->vRegClasses) Vec_IntFree( p->vRegClasses );
    if ( p->vBox1Cios )  Vec_IntFree( p->vBox1Cios );
    if ( p->pMemObjs )   Aig_MmFlexStop( p->pMemObjs, 0 );
    if ( p->pMemSops )   Aig_MmFlexStop( p->pMemSops, 0 );
    if ( p->pAig )       Aig_ManStop( p->pAig );
    if ( p->pManTime )   Tim_ManStop( p->pManTime );
    FREE( p->pModTable );
    free( p );
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
    Ntl_ManPrintTypes( p );
    fflush( stdout );
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

  Synopsis    [Saves the model type.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSaveBoxType( Ntl_Obj_t * pObj )
{
    Ntl_Mod_t * pModel = pObj->pImplem;
    int Number = 0;
    assert( Ntl_ObjIsBox(pObj) );
    Number |= (pModel->attrWhite << 0);
    Number |= (pModel->attrBox   << 1);
    Number |= (pModel->attrComb  << 2);
    Number |= (pModel->attrKeep  << 3);
    pModel->pMan->BoxTypes[Number]++;
}

/**Function*************************************************************

  Synopsis    [Saves the model type.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManPrintTypes( Ntl_Man_t * p )
{
    Ntl_Mod_t * pModel;
    Ntl_Obj_t * pObj;
    int i;
    pModel = Ntl_ManRootModel( p );
    if ( Ntl_ModelBoxNum(pModel) == 0 )
        return;
    printf( "BOX STATISTICS:\n" );
    Ntl_ModelForEachBox( pModel, pObj, i )
        Ntl_ManSaveBoxType( pObj );
    for ( i = 0; i < 15; i++ )
    {
        if ( !p->BoxTypes[i] )
            continue;
        printf( "%5d :", p->BoxTypes[i] );
        printf( " %s", ((i & 1) > 0)? "white": "black" );
        printf( " %s", ((i & 2) > 0)? "box  ": "logic" );
        printf( " %s", ((i & 4) > 0)? "comb ": "seq  " );
        printf( " %s", ((i & 8) > 0)? "keep ": "sweep" );
        printf( "\n" );
    }
    printf( "Total box instances = %6d.\n\n", Ntl_ModelBoxNum(pModel) );
    for ( i = 0; i < 15; i++ )
        p->BoxTypes[i] = 0;
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
    p->attrBox     = 1;
    p->attrComb    = 1;
    p->attrWhite   = 1;
    p->attrKeep    = 0;
    p->attrNoMerge = 0;
    p->pMan  = pMan;
    p->pName = Ntl_ManStoreName( p->pMan, pName );
    p->vObjs = Vec_PtrAlloc( 100 );
    p->vPis  = Vec_PtrAlloc( 10 );
    p->vPos  = Vec_PtrAlloc( 10 ); 
    // start the table
    p->nTableSize = Aig_PrimeCudd( 100 );
    p->pTable = ALLOC( Ntl_Net_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Ntl_Net_t *) * p->nTableSize );
    // add model to the table
    if ( !Ntl_ManAddModel( pMan, p ) )
    {
        Ntl_ModelFree( p );
        return NULL;
    }
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
        {
            ((Ntl_Obj_t *)pObj->pCopy)->LatchId = pObj->LatchId;
            ((Ntl_Obj_t *)pObj->pCopy)->pClock = pObj->pClock->pCopy;
        }
    }
    pModelNew->vDelays = pModelOld->vDelays? Vec_IntDup( pModelOld->vDelays ) : NULL;
    pModelNew->vTimeInputs = pModelOld->vTimeInputs? Vec_IntDup( pModelOld->vTimeInputs ) : NULL;
    pModelNew->vTimeOutputs = pModelOld->vTimeOutputs? Vec_IntDup( pModelOld->vTimeOutputs ) : NULL;
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
    pModelNew->attrWhite = pModelOld->attrWhite;
    pModelNew->attrBox     = pModelOld->attrBox;
    pModelNew->attrComb     = pModelOld->attrComb;
    pModelNew->attrKeep     = pModelOld->attrKeep;
    Ntl_ModelForEachObj( pModelOld, pObj, i )
        pObj->pCopy = Ntl_ModelDupObj( pModelNew, pObj );
    Ntl_ModelForEachNet( pModelOld, pNet, i )
    {
        pNet->pCopy = Ntl_ModelFindOrCreateNet( pModelNew, pNet->pName );
        if ( pNet->pDriver == NULL )
        {
            assert( !pModelOld->attrWhite );
            continue;
        }
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
        {
            ((Ntl_Obj_t *)pObj->pCopy)->LatchId = pObj->LatchId;
            ((Ntl_Obj_t *)pObj->pCopy)->pClock = pObj->pClock? pObj->pClock->pCopy : NULL;
        }
        if ( Ntl_ObjIsNode(pObj) )
            ((Ntl_Obj_t *)pObj->pCopy)->pSop = Ntl_ManStoreSop( pManNew->pMemSops, pObj->pSop );
    }
    pModelNew->vDelays = pModelOld->vDelays? Vec_IntDup( pModelOld->vDelays ) : NULL;
    pModelNew->vTimeInputs = pModelOld->vTimeInputs? Vec_IntDup( pModelOld->vTimeInputs ) : NULL;
    pModelNew->vTimeOutputs = pModelOld->vTimeOutputs? Vec_IntDup( pModelOld->vTimeOutputs ) : NULL;
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
    assert( Ntl_ModelCheckNetsAreNotMarked(p) );
    if ( p->vTimeOutputs )  Vec_IntFree( p->vTimeOutputs );
    if ( p->vTimeInputs )   Vec_IntFree( p->vTimeInputs );
    if ( p->vDelays )       Vec_IntFree( p->vDelays );
    Vec_PtrFree( p->vObjs );
    Vec_PtrFree( p->vPis );
    Vec_PtrFree( p->vPos );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Create model equal to the latch with the given init value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ManCreateLatchModel( Ntl_Man_t * pMan, int Init )
{
    char Name[100];
    Ntl_Mod_t * pModel;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNetLi, * pNetLo;
    // create model
    sprintf( Name, "%s%d", "latch", Init );
    pModel = Ntl_ModelAlloc( pMan, Name );
    pModel->attrWhite = 1;
    pModel->attrBox   = 1;
    pModel->attrComb  = 0;
    pModel->attrKeep  = 0;
    // create primary input
    pObj = Ntl_ModelCreatePi( pModel );
    pNetLi = Ntl_ModelFindOrCreateNet( pModel, "li" );
    Ntl_ModelSetNetDriver( pObj, pNetLi );
    // create latch 
    pObj = Ntl_ModelCreateLatch( pModel );
    pObj->LatchId.regInit = Init;
    pObj->pFanio[0] = pNetLi;
    // create primary output
    pNetLo = Ntl_ModelFindOrCreateNet( pModel, "lo" );
    Ntl_ModelSetNetDriver( pObj, pNetLo );
    pObj = Ntl_ModelCreatePo( pModel, pNetLo );
    // set timing information
    pModel->vTimeInputs = Vec_IntAlloc( 2 );
    Vec_IntPush( pModel->vTimeInputs, -1 );
    Vec_IntPush( pModel->vTimeInputs, Aig_Float2Int(0.0) );        
    pModel->vTimeOutputs = Vec_IntAlloc( 2 );
    Vec_IntPush( pModel->vTimeOutputs, -1 );
    Vec_IntPush( pModel->vTimeOutputs, Aig_Float2Int(0.0) );        
    return pModel;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


