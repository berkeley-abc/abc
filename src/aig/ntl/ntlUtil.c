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

  Synopsis    [Removes the CO drivers that are bufs/invs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects [This procedure does not work because the internal net
  (pNetFanin) may have other drivers.]

  SeeAlso     []

***********************************************************************/
int Ntl_ManTransformCoDrivers( Ntl_Man_t * p )
{
    Vec_Ptr_t * vCoNets;
    Ntl_Net_t * pNetCo, * pNetFanin;
    Ntl_Obj_t * pObj;
    Ntl_Mod_t * pRoot;
    int i, k, Counter;
    pRoot = Ntl_ManRootModel( p );
    // collect the nets of the root model
    vCoNets = Vec_PtrAlloc( 1000 );
    Ntl_ModelForEachPo( pRoot, pObj, i )
        if ( !Ntl_ObjFanin0(pObj)->fMark )
        {
            Ntl_ObjFanin0(pObj)->fMark = 1;
            Vec_PtrPush( vCoNets, Ntl_ObjFanin0(pObj) );
        }
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        if ( !Ntl_ObjFanin0(pObj)->fMark )
        {
            Ntl_ObjFanin0(pObj)->fMark = 1;
            Vec_PtrPush( vCoNets, Ntl_ObjFanin0(pObj) );
        }
    Ntl_ModelForEachBox( pRoot, pObj, k )
    Ntl_ObjForEachFanin( pObj, pNetCo, i )
        if ( !pNetCo->fMark )
        {
            pNetCo->fMark = 1;
            Vec_PtrPush( vCoNets, pNetCo );
        }
    // check the nets
    Vec_PtrForEachEntry( vCoNets, pNetCo, i )
    {
        if ( !Ntl_ObjIsNode(pNetCo->pDriver) )
            continue;
        if ( Ntl_ObjFaninNum(pNetCo->pDriver) != 1 )
            break;
        pNetFanin = Ntl_ObjFanin0(pNetCo->pDriver);
        if ( !Ntl_ObjIsNode(pNetFanin->pDriver) )
            break;
    }
    if ( i < Vec_PtrSize(vCoNets) )
    {
        Vec_PtrFree( vCoNets );
        return 0;
    }


    // remove the buffers/inverters
    Counter = 0;
    Vec_PtrForEachEntry( vCoNets, pNetCo, i )
    {
        pNetCo->fMark = 0;
        if ( !Ntl_ObjIsNode(pNetCo->pDriver) )
            continue;
        // if this net is driven by an interver
        // set the complemented attribute of the CO
        assert( Ntl_ObjFaninNum(pNetCo->pDriver) == 1 );
        pNetCo->fCompl = (int)(pNetCo->pDriver->pSop[0] == '0');
        // remove the driver
        Vec_PtrWriteEntry( pRoot->vObjs, pNetCo->pDriver->Id, NULL );
        // remove the net
        pNetFanin = Ntl_ObjFanin0(pNetCo->pDriver);
        Ntl_ModelDeleteNet( pRoot, pNetFanin );
        // make the CO net point to the new driver
        assert( Ntl_ObjIsNode(pNetFanin->pDriver) );
        pNetCo->pDriver = NULL;
        pNetFanin->pDriver->pFanio[pNetFanin->pDriver->nFanins] = NULL;
        Ntl_ModelSetNetDriver( pNetFanin->pDriver, pNetCo );
        Counter++;
    }
    Vec_PtrFree( vCoNets );
    pRoot->nObjs[NTL_OBJ_LUT1] -= Counter;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Connects COs to the internal nodes other than inv/bufs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects [This procedure does not work because the internal net
  (pNetFanin) may have other drivers.]

  SeeAlso     []

***********************************************************************/
int Ntl_ManReconnectCoDriverOne( Ntl_Net_t * pNetCo )
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
    // set the complemented attribute of the net
    pNetCo->fCompl = (int)(pNetCo->pDriver->pSop[0] == '0');
    // drive the CO net with the second-generation driver
    pNetCo->pDriver = NULL;
    pNetFanin->pDriver->pFanio[pNetFanin->pDriver->nFanins] = NULL;
    if ( !Ntl_ModelSetNetDriver( pNetFanin->pDriver, pNetCo ) )
        printf( "Ntl_ManReconnectCoDriverOne(): Cannot connect the net.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Connects COs to the internal nodes other than inv/bufs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManReconnectCoDrivers( Ntl_Man_t * p )
{
    Ntl_Net_t * pNetCo;
    Ntl_Obj_t * pObj;
    Ntl_Mod_t * pRoot;
    int i, k, Counter;
    Counter = 0;
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachPo( pRoot, pObj, i )
        Counter += Ntl_ManReconnectCoDriverOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        Counter += Ntl_ManReconnectCoDriverOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachBox( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNetCo, k )
            Counter += Ntl_ManReconnectCoDriverOne( pNetCo );
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


