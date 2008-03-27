/**CFile****************************************************************

  FileName    [ntkObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Manipulation of objects.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkObj.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates an object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateObj( Ntk_Man_t * p, int nFanins, int nFanouts )
{
    Ntk_Obj_t * pObj;
    pObj = (Ntk_Obj_t *)Aig_MmFlexEntryFetch( p->pMemObjs, sizeof(Ntk_Obj_t) + (nFanins + nFanouts + p->nFanioPlus) * sizeof(Ntk_Obj_t *) );
    memset( pObj, 0, sizeof(Ntk_Obj_t) );
    pObj->Id = Vec_PtrSize( p->vObjs );
    Vec_PtrPush( p->vObjs, pObj );
    pObj->pMan        = p;
    pObj->nFanioAlloc = nFanins + nFanouts + p->nFanioPlus;
    return pObj;
}


/**Function*************************************************************

  Synopsis    [Creates a primary input.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateCi( Ntk_Man_t * p, int nFanouts )
{
    Ntk_Obj_t * pObj;
    pObj = Ntk_ManCreateObj( p, 1, nFanouts );
    pObj->PioId = Vec_PtrSize( p->vCis );
    Vec_PtrPush( p->vCis, pObj );
    pObj->Type = NTK_OBJ_CI;
    p->nObjs[NTK_OBJ_CI]++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates a primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateCo( Ntk_Man_t * p )
{
    Ntk_Obj_t * pObj;
    pObj = Ntk_ManCreateObj( p, 1, 1 );
    pObj->PioId = Vec_PtrSize( p->vCos );
    Vec_PtrPush( p->vCos, pObj );
    pObj->Type = NTK_OBJ_CO;
    p->nObjs[NTK_OBJ_CO]++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates a latch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateLatch( Ntk_Man_t * p )
{
    Ntk_Obj_t * pObj;
    pObj = Ntk_ManCreateObj( p, 1, 1 );
    pObj->Type = NTK_OBJ_LATCH;
    p->nObjs[NTK_OBJ_LATCH]++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates a node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateNode( Ntk_Man_t * p, int nFanins, int nFanouts )
{
    Ntk_Obj_t * pObj;
    pObj = Ntk_ManCreateObj( p, nFanins, nFanouts );
    pObj->Type = NTK_OBJ_NODE;
    p->nObjs[NTK_OBJ_NODE]++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates a box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Obj_t * Ntk_ManCreateBox( Ntk_Man_t * p, int nFanins, int nFanouts )
{
    Ntk_Obj_t * pObj;
    pObj = Ntk_ManCreateObj( p, nFanins, nFanouts );
    pObj->Type = NTK_OBJ_BOX;
    p->nObjs[NTK_OBJ_BOX]++;
    return pObj;
}


/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDeleteNode( Ntk_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes = pObj->pMan->vTemp;
    Ntk_Obj_t * pTemp;
    int i;
    // delete fanins and fanouts
    Ntk_ObjCollectFanouts( pObj, vNodes );
    Vec_PtrForEachEntry( vNodes, pTemp, i )
        Ntk_ObjDeleteFanin( pTemp, pObj );
    Ntk_ObjCollectFanins( pObj, vNodes );
    Vec_PtrForEachEntry( vNodes, pTemp, i )
        Ntk_ObjDeleteFanin( pObj, pTemp );
    // remove from the list of objects
    Vec_PtrWriteEntry( pObj->pMan->vObjs, pObj->Id, NULL );
    pObj->pMan->nObjs[pObj->Type]--;
    memset( pObj, 0, sizeof(Ntk_Obj_t) );
    pObj->Id = -1;
}

/**Function*************************************************************

  Synopsis    [Deletes the node and MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDeleteNode_rec( Ntk_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes;
    int i;
    assert( !Ntk_ObjIsCi(pObj) );
    assert( Ntk_ObjFanoutNum(pObj) == 0 );
    vNodes = Vec_PtrAlloc( 100 );
    Ntk_ObjCollectFanins( pObj, vNodes );
    Ntk_ManDeleteNode( pObj );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Ntk_ObjIsNode(pObj) && Ntk_ObjFanoutNum(pObj) == 0 )
            Ntk_ManDeleteNode_rec( pObj );
    Vec_PtrFree( vNodes );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


