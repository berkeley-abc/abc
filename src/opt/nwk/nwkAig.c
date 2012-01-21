/**CFile****************************************************************

  FileName    [nwkAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Translating of AIG into the network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts AIG into the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Nwk_ManDeriveFromAig( Aig_Man_t * p )
{
    Nwk_Man_t * pNtk;
    Aig_Obj_t * pObj;
    int i;
    pNtk = Nwk_ManAlloc();
    pNtk->nFanioPlus = 0;
    Hop_ManStop( pNtk->pManHop );
    pNtk->pManHop = NULL;
    pNtk->pName = Abc_UtilStrsav( p->pName );
    pNtk->pSpec = Abc_UtilStrsav( p->pSpec );
    pObj = Aig_ManConst1(p);
    pObj->pData = Nwk_ManCreateNode( pNtk, 0, pObj->nRefs );
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Nwk_ManCreateCi( pNtk, pObj->nRefs );
    Aig_ManForEachNode( p, pObj, i )
    {
        pObj->pData = Nwk_ManCreateNode( pNtk, 2, pObj->nRefs );
        Nwk_ObjAddFanin( (Nwk_Obj_t *)pObj->pData, (Nwk_Obj_t *)Aig_ObjFanin0(pObj)->pData );
        Nwk_ObjAddFanin( (Nwk_Obj_t *)pObj->pData, (Nwk_Obj_t *)Aig_ObjFanin1(pObj)->pData );
    }
    Aig_ManForEachPo( p, pObj, i )
    {
        pObj->pData = Nwk_ManCreateCo( pNtk );
        Nwk_ObjAddFanin( (Nwk_Obj_t *)pObj->pData, (Nwk_Obj_t *)Aig_ObjFanin0(pObj)->pData );
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Nwk_ManDeriveRetimingCut( Aig_Man_t * p, int fForward, int fVerbose )
{ 
    Vec_Ptr_t * vNodes;
    Nwk_Man_t * pNtk;
    Nwk_Obj_t * pNode;
    Aig_Obj_t * pObj;
    int i;
    pNtk = Nwk_ManDeriveFromAig( p );
    if ( fForward )
        vNodes = Nwk_ManRetimeCutForward( pNtk, Aig_ManRegNum(p), fVerbose );
    else
        vNodes = Nwk_ManRetimeCutBackward( pNtk, Aig_ManRegNum(p), fVerbose );
    Aig_ManForEachObj( p, pObj, i )
        ((Nwk_Obj_t *)pObj->pData)->pCopy = pObj;
    Vec_PtrForEachEntry( Nwk_Obj_t *, vNodes, pNode, i )
        Vec_PtrWriteEntry( vNodes, i, pNode->pCopy );
    Nwk_ManFree( pNtk );
//    assert( Vec_PtrSize(vNodes) <= Aig_ManRegNum(p) );
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

