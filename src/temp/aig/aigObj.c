/**CFile****************************************************************

  FileName    [aigObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [Adding/removing objects.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aigObj.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates primary input.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ObjCreatePi( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    pObj = Aig_ManFetchMemory( p );
    pObj->Type = AIG_PI;
    Vec_PtrPush( p->vPis, pObj );
    p->nObjs[AIG_PI]++;
    p->nCreated++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates primary output with the given driver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ObjCreatePo( Aig_Man_t * p, Aig_Obj_t * pDriver )
{
    Aig_Obj_t * pObj;
    pObj = Aig_ManFetchMemory( p );
    pObj->Type = AIG_PO;
    Vec_PtrPush( p->vPos, pObj );
    // add connections
    pObj->pFanin0 = pDriver;
    if ( p->fRefCount )
        Aig_ObjRef( Aig_Regular(pDriver) );
    else
        pObj->nRefs = Aig_ObjLevel( Aig_Regular(pDriver) );
    // update node counters of the manager
    p->nObjs[AIG_PO]++;
    p->nCreated++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Create the new node assuming it does not exist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ObjCreate( Aig_Man_t * p, Aig_Obj_t * pGhost )
{
    Aig_Obj_t * pObj;
    assert( !Aig_IsComplement(pGhost) );
    assert( Aig_ObjIsNode(pGhost) );
    assert( pGhost == &p->Ghost );
    // get memory for the new object
    pObj = Aig_ManFetchMemory( p );
    pObj->Type = pGhost->Type;
    // add connections
    Aig_ObjConnect( p, pObj, pGhost->pFanin0, pGhost->pFanin1 );
    // update node counters of the manager
    p->nObjs[Aig_ObjType(pObj)]++;
    p->nCreated++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Connect the object to the fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjConnect( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFan0, Aig_Obj_t * pFan1 )
{
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsNode(pObj) );
    // add the first fanin
    pObj->pFanin0 = pFan0;
    pObj->pFanin1 = pFan1;
    // increment references of the fanins and add their fanouts
    if ( p->fRefCount )
    {
        if ( pFan0 != NULL )
            Aig_ObjRef( Aig_ObjFanin0(pObj) );
        if ( pFan1 != NULL )
            Aig_ObjRef( Aig_ObjFanin1(pObj) );
    }
    else
        pObj->nRefs = Aig_ObjLevelNew( pObj );
    // add the node to the structural hash table
    Aig_TableInsert( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Connect the object to the fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjDisconnect( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsNode(pObj) );
    // remove connections
    if ( pObj->pFanin0 != NULL )
        Aig_ObjDeref(Aig_ObjFanin0(pObj));
    if ( pObj->pFanin1 != NULL )
        Aig_ObjDeref(Aig_ObjFanin1(pObj));
    // remove the node from the structural hash table
    Aig_TableDelete( p, pObj );
    // add the first fanin
    pObj->pFanin0 = NULL;
    pObj->pFanin1 = NULL;
}

/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjDelete( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    assert( !Aig_ObjIsTerm(pObj) );
    assert( Aig_ObjRefs(pObj) == 0 );
    // update node counters of the manager
    p->nObjs[pObj->Type]--;
    p->nDeleted++;
    // remove connections
    Aig_ObjDisconnect( p, pObj );
    // remove PIs/POs from the arrays
    if ( Aig_ObjIsPi(pObj) )
        Vec_PtrRemove( p->vPis, pObj );
    // free the node
    Aig_ManRecycleMemory( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Deletes the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjDelete_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pFanin0, * pFanin1;
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsPi(pObj) )
        return;
    assert( Aig_ObjIsNode(pObj) );
    pFanin0 = Aig_ObjFanin0(pObj);
    pFanin1 = Aig_ObjFanin1(pObj);
    Aig_ObjDelete( p, pObj );
    if ( pFanin0 && !Aig_ObjIsNone(pFanin0) && Aig_ObjRefs(pFanin0) == 0 )
        Aig_ObjDelete_rec( p, pFanin0 );
    if ( pFanin1 && !Aig_ObjIsNone(pFanin1) && Aig_ObjRefs(pFanin1) == 0 )
        Aig_ObjDelete_rec( p, pFanin1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


