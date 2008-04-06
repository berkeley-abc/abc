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

  Synopsis    [Returns 1 if netlist was written by ABC with added bufs/invs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects []

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
    pRoot->nObjs[NTL_OBJ_NODE] -= Counter;
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


