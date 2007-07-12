/**CFile****************************************************************

  FileName    [aigObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Adding/removing objects.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigObj.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

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
    pObj->Type = AIG_OBJ_PI;
    Vec_PtrPush( p->vPis, pObj );
    p->nObjs[AIG_OBJ_PI]++;
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
    pObj->Type = AIG_OBJ_PO;
    Vec_PtrPush( p->vPos, pObj );
    // add connections
    Aig_ObjConnect( p, pObj, pDriver, NULL );
    // update node counters of the manager
    p->nObjs[AIG_OBJ_PO]++;
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
    assert( Aig_ObjIsHash(pGhost) );
    assert( pGhost == &p->Ghost );
    // get memory for the new object
    pObj = Aig_ManFetchMemory( p );
    pObj->Type = pGhost->Type;
    // add connections
    Aig_ObjConnect( p, pObj, pGhost->pFanin0, pGhost->pFanin1 );
    // update node counters of the manager
    p->nObjs[Aig_ObjType(pObj)]++;
    assert( pObj->pData == NULL );
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
    assert( !Aig_ObjIsPi(pObj) );
    // add the first fanin
    pObj->pFanin0 = pFan0;
    pObj->pFanin1 = pFan1;
    // increment references of the fanins and add their fanouts
    if ( pFan0 != NULL )
    {
        assert( Aig_ObjFanin0(pObj)->Type > 0 );
        Aig_ObjRef( Aig_ObjFanin0(pObj) );
    }
    if ( pFan1 != NULL )
    {
        assert( Aig_ObjFanin1(pObj)->Type > 0 );
        Aig_ObjRef( Aig_ObjFanin1(pObj) );
    }
    // set level and phase
    if ( pFan1 != NULL )
    {
        pObj->Level = Aig_ObjLevelNew( pObj );
        pObj->fPhase = Aig_ObjFaninPhase(pFan0) & Aig_ObjFaninPhase(pFan1);
    }
    else
    {
        pObj->Level = pFan0->Level;
        pObj->fPhase = Aig_ObjFaninPhase(pFan0);
    }
    // add the node to the structural hash table
    if ( Aig_ObjIsHash(pObj) )
        Aig_TableInsert( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Disconnects the object from the fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjDisconnect( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    // remove connections
    if ( pObj->pFanin0 != NULL )
        Aig_ObjDeref(Aig_ObjFanin0(pObj));
    if ( pObj->pFanin1 != NULL )
        Aig_ObjDeref(Aig_ObjFanin1(pObj));
    // remove the node from the structural hash table
    if ( Aig_ObjIsHash(pObj) )
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
    p->nObjs[pObj->Type]--;
    Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
    Aig_ManRecycleMemory( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Deletes the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjDelete_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int fFreeTop )
{
    Aig_Obj_t * pFanin0, * pFanin1;
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsPi(pObj) )
        return;
    assert( !Aig_ObjIsPo(pObj) );
    pFanin0 = Aig_ObjFanin0(pObj);
    pFanin1 = Aig_ObjFanin1(pObj);
    Aig_ObjDisconnect( p, pObj );
    if ( fFreeTop )
        Aig_ObjDelete( p, pObj );
    if ( pFanin0 && !Aig_ObjIsNone(pFanin0) && Aig_ObjRefs(pFanin0) == 0 )
        Aig_ObjDelete_rec( p, pFanin0, 1 );
    if ( pFanin1 && !Aig_ObjIsNone(pFanin1) && Aig_ObjRefs(pFanin1) == 0 )
        Aig_ObjDelete_rec( p, pFanin1, 1 );
}

/**Function*************************************************************

  Synopsis    [Replaces the first fanin of the node by the new fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjPatchFanin0( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFaninNew )
{
    Aig_Obj_t * pFaninOld;
    assert( !Aig_IsComplement(pObj) );
    pFaninOld = Aig_ObjFanin0(pObj);
    // decrement ref and remove fanout
    Aig_ObjDeref( pFaninOld );
    // update the fanin
    pObj->pFanin0 = pFaninNew;
    // increment ref and add fanout
    Aig_ObjRef( Aig_Regular(pFaninNew) );
    // get rid of old fanin
    if ( !Aig_ObjIsPi(pFaninOld) && !Aig_ObjIsConst1(pFaninOld) && Aig_ObjRefs(pFaninOld) == 0 )
        Aig_ObjDelete_rec( p, pFaninOld, 1 );
}

/**Function*************************************************************

  Synopsis    [Replaces one object by another.]

  Description [Both objects are currently in the manager. The new object
  (pObjNew) should be used instead of the old object (pObjOld). If the 
  new object is complemented or used, the buffer is added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjReplace( Aig_Man_t * p, Aig_Obj_t * pObjOld, Aig_Obj_t * pObjNew, int fNodesOnly )
{
    Aig_Obj_t * pObjNewR = Aig_Regular(pObjNew);
    // the object to be replaced cannot be complemented
    assert( !Aig_IsComplement(pObjOld) );
    // the object to be replaced cannot be a terminal
    assert( !Aig_ObjIsPi(pObjOld) && !Aig_ObjIsPo(pObjOld) );
    // the object to be used cannot be a buffer or a PO
    assert( !Aig_ObjIsBuf(pObjNewR) && !Aig_ObjIsPo(pObjNewR) );
    // the object cannot be the same
    assert( pObjOld != pObjNewR );
    // make sure object is not pointing to itself
    assert( pObjOld != Aig_ObjFanin0(pObjNewR) );
    assert( pObjOld != Aig_ObjFanin1(pObjNewR) );
    // recursively delete the old node - but leave the object there
    pObjNewR->nRefs++;
    Aig_ObjDelete_rec( p, pObjOld, 0 );
    pObjNewR->nRefs--;
    // if the new object is complemented or already used, create a buffer
    p->nObjs[pObjOld->Type]--;
    if ( Aig_IsComplement(pObjNew) || Aig_ObjRefs(pObjNew) > 0 || (fNodesOnly && !Aig_ObjIsNode(pObjNew)) )
    {
        pObjOld->Type = AIG_OBJ_BUF;
        Aig_ObjConnect( p, pObjOld, pObjNew, NULL );
    }
    else
    {
        Aig_Obj_t * pFanin0 = pObjNew->pFanin0;
        Aig_Obj_t * pFanin1 = pObjNew->pFanin1;
        pObjOld->Type = pObjNew->Type;
        Aig_ObjDisconnect( p, pObjNew );
        Aig_ObjConnect( p, pObjOld, pFanin0, pFanin1 );
        Aig_ObjDelete( p, pObjNew );
    }
    p->nObjs[pObjOld->Type]++;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


