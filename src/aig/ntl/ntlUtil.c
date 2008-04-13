/**CFile****************************************************************

  FileName    [ntlUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts COs that are connected to the internal nodes through invs/bufs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCountLut1( Ntl_Mod_t * pRoot )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachNode( pRoot, pObj, i )
        if ( Ntl_ObjFaninNum(pObj) == 1 )
            Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Connects COs to the internal nodes other than inv/bufs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCountSimpleCoDriversOne( Ntl_Net_t * pNetCo )
{
    Ntl_Net_t * pNetFanin;
    // skip the case when the net is not driven by a node
    if ( !Ntl_ObjIsNode(pNetCo->pDriver) )
        return 0;
    // skip the case when the node is not an inv/buf
    if ( Ntl_ObjFaninNum(pNetCo->pDriver) != 1 )
        return 0;
    // skip the case when the second-generation driver is not a node
    pNetFanin = Ntl_ObjFanin0(pNetCo->pDriver);
    if ( !Ntl_ObjIsNode(pNetFanin->pDriver) )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts COs that are connected to the internal nodes through invs/bufs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCountSimpleCoDrivers( Ntl_Man_t * p )
{
    Ntl_Net_t * pNetCo;
    Ntl_Obj_t * pObj;
    Ntl_Mod_t * pRoot;
    int i, k, Counter;
    Counter = 0;
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachPo( pRoot, pObj, i )
        Counter += Ntl_ManCountSimpleCoDriversOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        Counter += Ntl_ManCountSimpleCoDriversOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachBox( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNetCo, k )
            Counter += Ntl_ManCountSimpleCoDriversOne( pNetCo );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Derives the array of CI names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManCollectCiNames( Ntl_Man_t * p )
{
    Vec_Ptr_t * vNames;
    Ntl_Net_t * pNet;
    int i;
    vNames = Vec_PtrAlloc( 1000 );
    Ntl_ManForEachCiNet( p, pNet, i )
        Vec_PtrPush( vNames, pNet->pName );
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Derives the array of CI names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManCollectCoNames( Ntl_Man_t * p )
{
    Vec_Ptr_t * vNames;
    Ntl_Net_t * pNet;
    int i;
    vNames = Vec_PtrAlloc( 1000 );
    Ntl_ManForEachCoNet( p, pNet, i )
        Vec_PtrPush( vNames, pNet->pName );
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Marks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManMarkCiCoNets( Ntl_Man_t * p )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->fMark = 1;
    Ntl_ManForEachCoNet( p, pNet, i )
        pNet->fMark = 1;
}

/**Function*************************************************************

  Synopsis    [Unmarks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManUnmarkCiCoNets( Ntl_Man_t * p )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->fMark = 0;
    Ntl_ManForEachCoNet( p, pNet, i )
        pNet->fMark = 0;
}

/**Function*************************************************************

  Synopsis    [Unmarks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCheckNetsAreNotMarked( Ntl_Mod_t * pModel )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ModelForEachNet( pModel, pNet, i )
        assert( pNet->fMark == 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Convert initial values of registers to be zero.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSetZeroInitValues( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        pObj->LatchId &= ~3;
}

/**Function*************************************************************

  Synopsis    [Transforms the netlist to have latches with const-0 init-values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManAddInverters( Ntl_Obj_t * pObj )
{
    char * pStore;
    Ntl_Mod_t * pRoot = pObj->pModel;
    Ntl_Man_t * pMan = pRoot->pMan;
    Ntl_Net_t * pNetLo, * pNetLi, * pNetLoInv, * pNetLiInv;
    Ntl_Obj_t * pNode;
    int nLength, RetValue;
    assert( (pObj->LatchId & 3) == 1 );
    // get the nets
    pNetLi = Ntl_ObjFanin0(pObj);
    pNetLo = Ntl_ObjFanout0(pObj);
    // get storage for net names
    nLength = strlen(pNetLi->pName) + strlen(pNetLo->pName) + 10; 
    pStore = Aig_MmFlexEntryFetch( pMan->pMemSops, nLength );
    // create input interter
    pNode = Ntl_ModelCreateNode( pRoot, 1 );
    pNode->pSop = Ntl_ManStoreSop( pMan->pMemSops, "0 1\n" );
    Ntl_ObjSetFanin( pNode, pNetLi, 0 );
    // create input net
    strcpy( pStore, pNetLi->pName );
    strcat( pStore, "_inv" );
    if ( Ntl_ModelFindNet( pRoot, pStore ) )
    {
        printf( "Ntl_ManTransformInitValues(): Internal error! Cannot create net with LI-name + _inv\n" );
        return;
    }
    pNetLiInv = Ntl_ModelFindOrCreateNet( pRoot, pStore );
    RetValue = Ntl_ModelSetNetDriver( pNode, pNetLiInv );
    assert( RetValue );
    // connect latch to the input net
    Ntl_ObjSetFanin( pObj, pNetLiInv, 0 );
    // disconnect latch from the output net
    RetValue = Ntl_ModelClearNetDriver( pObj, pNetLo );
    assert( RetValue );
    // create the output net
    strcpy( pStore, pNetLo->pName );
    strcat( pStore, "_inv" );
    if ( Ntl_ModelFindNet( pRoot, pStore ) )
    {
        printf( "Ntl_ManTransformInitValues(): Internal error! Cannot create net with LO-name + _inv\n" );
        return;
    }
    pNetLoInv = Ntl_ModelFindOrCreateNet( pRoot, pStore );
    RetValue = Ntl_ModelSetNetDriver( pObj, pNetLoInv );
    assert( RetValue );
    // create output interter
    pNode = Ntl_ModelCreateNode( pRoot, 1 );
    pNode->pSop = Ntl_ManStoreSop( pMan->pMemSops, "0 1\n" );
    Ntl_ObjSetFanin( pNode, pNetLoInv, 0 );
    // redirect the old output net
    RetValue = Ntl_ModelSetNetDriver( pNode, pNetLo );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Transforms the netlist to have latches with const-0 init-values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManTransformInitValues( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        if ( (pObj->LatchId & 3) == 1 )
            Ntl_ManAddInverters( pObj );
        pObj->LatchId &= ~3;
    }

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


