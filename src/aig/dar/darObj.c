/**CFile****************************************************************

  FileName    [darObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Adding/removing objects.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darObj.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

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
Dar_Obj_t * Dar_ObjCreatePi( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    pObj = Dar_ManFetchMemory( p );
    pObj->Type = DAR_AIG_PI;
    Vec_PtrPush( p->vPis, pObj );
    p->nObjs[DAR_AIG_PI]++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates primary output with the given driver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_ObjCreatePo( Dar_Man_t * p, Dar_Obj_t * pDriver )
{
    Dar_Obj_t * pObj;
    pObj = Dar_ManFetchMemory( p );
    pObj->Type = DAR_AIG_PO;
    Vec_PtrPush( p->vPos, pObj );
    // add connections
    Dar_ObjConnect( p, pObj, pDriver, NULL );
    // update node counters of the manager
    p->nObjs[DAR_AIG_PO]++;
    return pObj;
}


/**Function*************************************************************

  Synopsis    [Create the new node assuming it does not exist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_ObjCreate( Dar_Man_t * p, Dar_Obj_t * pGhost )
{
    Dar_Obj_t * pObj;
    assert( !Dar_IsComplement(pGhost) );
    assert( Dar_ObjIsHash(pGhost) );
    assert( pGhost == &p->Ghost );
    // get memory for the new object
    pObj = Dar_ManFetchMemory( p );
    pObj->Type = pGhost->Type;
    // add connections
    Dar_ObjConnect( p, pObj, pGhost->pFanin0, pGhost->pFanin1 );
    // update node counters of the manager
    p->nObjs[Dar_ObjType(pObj)]++;
    assert( pObj->pData == NULL );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Connect the object to the fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjConnect( Dar_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pFan0, Dar_Obj_t * pFan1 )
{
    assert( !Dar_IsComplement(pObj) );
    assert( !Dar_ObjIsPi(pObj) );
    // add the first fanin
    pObj->pFanin0 = pFan0;
    pObj->pFanin1 = pFan1;
    // increment references of the fanins and add their fanouts
    if ( pFan0 != NULL )
    {
        assert( Dar_ObjFanin0(pObj)->Type > 0 );
        Dar_ObjRef( Dar_ObjFanin0(pObj) );
    }
    if ( pFan1 != NULL )
    {
        assert( Dar_ObjFanin1(pObj)->Type > 0 );
        Dar_ObjRef( Dar_ObjFanin1(pObj) );
    }
    // set level and phase
    if ( pFan1 != NULL )
    {
        pObj->Level = Dar_ObjLevelNew( pObj );
        pObj->fPhase = Dar_ObjFaninPhase(pFan0) & Dar_ObjFaninPhase(pFan1);
    }
    else
    {
        pObj->Level = pFan0->Level;
        pObj->fPhase = Dar_ObjFaninPhase(pFan0);
    }
    // add the node to the structural hash table
    if ( Dar_ObjIsHash(pObj) )
        Dar_TableInsert( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Disconnects the object from the fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjDisconnect( Dar_Man_t * p, Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    // remove connections
    if ( pObj->pFanin0 != NULL )
        Dar_ObjDeref(Dar_ObjFanin0(pObj));
    if ( pObj->pFanin1 != NULL )
        Dar_ObjDeref(Dar_ObjFanin1(pObj));
    // remove the node from the structural hash table
    if ( Dar_ObjIsHash(pObj) )
        Dar_TableDelete( p, pObj );
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
void Dar_ObjDelete( Dar_Man_t * p, Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    assert( !Dar_ObjIsTerm(pObj) );
    assert( Dar_ObjRefs(pObj) == 0 );
    p->nObjs[pObj->Type]--;
    Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
    Dar_ManRecycleMemory( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Deletes the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjDelete_rec( Dar_Man_t * p, Dar_Obj_t * pObj, int fFreeTop )
{
    Dar_Obj_t * pFanin0, * pFanin1;
    assert( !Dar_IsComplement(pObj) );
    if ( Dar_ObjIsConst1(pObj) || Dar_ObjIsPi(pObj) )
        return;
    assert( !Dar_ObjIsPo(pObj) );
    pFanin0 = Dar_ObjFanin0(pObj);
    pFanin1 = Dar_ObjFanin1(pObj);
    Dar_ObjDisconnect( p, pObj );
    if ( fFreeTop )
        Dar_ObjDelete( p, pObj );
    if ( pFanin0 && !Dar_ObjIsNone(pFanin0) && Dar_ObjRefs(pFanin0) == 0 )
        Dar_ObjDelete_rec( p, pFanin0, 1 );
    if ( pFanin1 && !Dar_ObjIsNone(pFanin1) && Dar_ObjRefs(pFanin1) == 0 )
        Dar_ObjDelete_rec( p, pFanin1, 1 );
}

/**Function*************************************************************

  Synopsis    [Replaces the first fanin of the node by the new fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjPatchFanin0( Dar_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pFaninNew )
{
    Dar_Obj_t * pFaninOld;
    assert( !Dar_IsComplement(pObj) );
    pFaninOld = Dar_ObjFanin0(pObj);
    // decrement ref and remove fanout
    Dar_ObjDeref( pFaninOld );
    // update the fanin
    pObj->pFanin0 = pFaninNew;
    // increment ref and add fanout
    Dar_ObjRef( Dar_Regular(pFaninNew) );
    // get rid of old fanin
    if ( !Dar_ObjIsPi(pFaninOld) && !Dar_ObjIsConst1(pFaninOld) && Dar_ObjRefs(pFaninOld) == 0 )
        Dar_ObjDelete_rec( p, pFaninOld, 1 );
}

/**Function*************************************************************

  Synopsis    [Replaces one object by another.]

  Description [Both objects are currently in the manager. The new object
  (pObjNew) should be used instead of the old object (pObjOld). If the 
  new object is complemented or used, the buffer is added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjReplace( Dar_Man_t * p, Dar_Obj_t * pObjOld, Dar_Obj_t * pObjNew, int fNodesOnly )
{
    Dar_Obj_t * pObjNewR = Dar_Regular(pObjNew);
    // the object to be replaced cannot be complemented
    assert( !Dar_IsComplement(pObjOld) );
    // the object to be replaced cannot be a terminal
    assert( !Dar_ObjIsPi(pObjOld) && !Dar_ObjIsPo(pObjOld) );
    // the object to be used cannot be a buffer or a PO
    assert( !Dar_ObjIsBuf(pObjNewR) && !Dar_ObjIsPo(pObjNewR) );
    // the object cannot be the same
    assert( pObjOld != pObjNewR );
    // make sure object is not pointing to itself
    assert( pObjOld != Dar_ObjFanin0(pObjNewR) );
    assert( pObjOld != Dar_ObjFanin1(pObjNewR) );
    // recursively delete the old node - but leave the object there
    pObjNewR->nRefs++;
    Dar_ObjDelete_rec( p, pObjOld, 0 );
    pObjNewR->nRefs--;
    // if the new object is complemented or already used, create a buffer
    p->nObjs[pObjOld->Type]--;
    if ( Dar_IsComplement(pObjNew) || Dar_ObjRefs(pObjNew) > 0 || (fNodesOnly && !Dar_ObjIsNode(pObjNew)) )
    {
        pObjOld->Type = DAR_AIG_BUF;
        Dar_ObjConnect( p, pObjOld, pObjNew, NULL );
    }
    else
    {
        Dar_Obj_t * pFanin0 = pObjNew->pFanin0;
        Dar_Obj_t * pFanin1 = pObjNew->pFanin1;
        pObjOld->Type = pObjNew->Type;
        Dar_ObjDisconnect( p, pObjNew );
        Dar_ObjConnect( p, pObjOld, pFanin0, pFanin1 );
        Dar_ObjDelete( p, pObjNew );
    }
    p->nObjs[pObjOld->Type]++;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


