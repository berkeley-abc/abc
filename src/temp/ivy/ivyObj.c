/**CFile****************************************************************

  FileName    [ivyObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Adding/removing objects.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyObj.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create the new node assuming it does not exist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjCreate( Ivy_Obj_t * pGhost )
{
    Ivy_Man_t * p = Ivy_ObjMan(pGhost);
    Ivy_Obj_t * pObj;
    assert( !Ivy_IsComplement(pGhost) );
    assert( Ivy_ObjIsGhost(pGhost) );

    assert( Ivy_TableLookup(pGhost) == NULL );

    // realloc the node array
    if ( p->ObjIdNext == p->nObjsAlloc )
    {
        Ivy_ManGrow( p );
        pGhost = Ivy_ManGhost( p );
    }
    // get memory for the new object
    if ( Vec_IntSize(p->vFree) > 0 )
        pObj = p->pObjs + Vec_IntPop(p->vFree);
    else
        pObj = p->pObjs + p->ObjIdNext++;
    assert( pObj->Id == pObj - p->pObjs );
    assert( Ivy_ObjIsNone(pObj) );
    // add basic info (fanins, compls, type, init)
    Ivy_ObjOverwrite( pObj, pGhost );
    // increment references of the fanins
    Ivy_ObjRefsInc( Ivy_ObjFanin0(pObj) );
    Ivy_ObjRefsInc( Ivy_ObjFanin1(pObj) );
    // add the node to the structural hash table
    Ivy_TableInsert( pObj );
    // compute level
    if ( Ivy_ObjIsNode(pObj) )
        pObj->Level = Ivy_ObjLevelNew(pObj);
    else if ( Ivy_ObjIsLatch(pObj) )
        pObj->Level = 0;
    else if ( Ivy_ObjIsOneFanin(pObj) )
        pObj->Level = Ivy_ObjFanin0(pObj)->Level;
    else if ( !Ivy_ObjIsPi(pObj) )
        assert( 0 );
    // mark the fanins in a special way if the node is EXOR
    if ( Ivy_ObjIsExor(pObj) )
    {
        Ivy_ObjFanin0(pObj)->fExFan = 1;
        Ivy_ObjFanin1(pObj)->fExFan = 1;
    }
    // add PIs/POs to the arrays
    if ( Ivy_ObjIsPi(pObj) )
        Vec_IntPush( p->vPis, pObj->Id );
    else if ( Ivy_ObjIsPo(pObj) )
        Vec_IntPush( p->vPos, pObj->Id );
    // update node counters of the manager
    p->nObjs[Ivy_ObjType(pObj)]++;
    p->nCreated++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Create the new node assuming it does not exist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjCreateExt( Ivy_Man_t * p, Ivy_Type_t Type )
{
    Ivy_Obj_t * pObj;
    assert( Type == IVY_ANDM || Type == IVY_EXORM || Type == IVY_LUT ); 
    // realloc the node array
    if ( p->ObjIdNext == p->nObjsAlloc )
        Ivy_ManGrow( p );
    // create the new node
    pObj = p->pObjs + p->ObjIdNext;
    assert( pObj->Id == p->ObjIdNext );
    p->ObjIdNext++;
    pObj->Type = Type;
    // update node counters of the manager
    p->nObjs[Type]++;
    p->nCreated++;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Connect the object to the fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjConnect( Ivy_Obj_t * pObj, Ivy_Obj_t * pFanin )
{
    assert( !Ivy_IsComplement(pObj) );
    assert( Ivy_ObjIsOneFanin(pObj) );
    assert( Ivy_ObjFaninId0(pObj) == 0 );
    // add the first fanin
    pObj->fComp0 = Ivy_IsComplement(pFanin);
    pObj->Fanin0 = Ivy_Regular(pFanin)->Id;
    // increment references of the fanins
    Ivy_ObjRefsInc( Ivy_ObjFanin0(pObj) );
    // add the node to the structural hash table
    Ivy_TableInsert( pObj );
}

/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjDelete( Ivy_Obj_t * pObj, int fFreeTop )
{
    Ivy_Man_t * p;
    assert( !Ivy_IsComplement(pObj) );
    assert( Ivy_ObjRefs(pObj) == 0 );
    // remove connections
    Ivy_ObjRefsDec(Ivy_ObjFanin0(pObj));
    Ivy_ObjRefsDec(Ivy_ObjFanin1(pObj));
    // remove the node from the structural hash table
    Ivy_TableDelete( pObj );
    // update node counters of the manager
    p = Ivy_ObjMan(pObj);
    p->nObjs[pObj->Type]--;
    p->nDeleted++;
    // remove PIs/POs from the arrays
    if ( Ivy_ObjIsPi(pObj) )
        Vec_IntRemove( p->vPis, pObj->Id );
    else if ( Ivy_ObjIsPo(pObj) )
        Vec_IntRemove( p->vPos, pObj->Id );
    // recorde the deleted node
    if ( p->fRecording )
        Ivy_ManUndoRecord( p, pObj );
    // clean the node's memory
    Ivy_ObjClean( pObj );
    // remember the entry
    if ( fFreeTop )
        Vec_IntPush( p->vFree, pObj->Id );
}

/**Function*************************************************************

  Synopsis    [Deletes the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjDelete_rec( Ivy_Obj_t * pObj, int fFreeTop )
{
    Ivy_Obj_t * pFanin0, * pFanin1;
    assert( !Ivy_IsComplement(pObj) );
    assert( !Ivy_ObjIsPo(pObj) && !Ivy_ObjIsNone(pObj) );
    if ( Ivy_ObjIsConst1(pObj) || Ivy_ObjIsPi(pObj) )
        return;
    pFanin0 = Ivy_ObjFanin0(pObj);
    pFanin1 = Ivy_ObjFanin1(pObj);
    Ivy_ObjDelete( pObj, fFreeTop );
    if ( !Ivy_ObjIsNone(pFanin0) && Ivy_ObjRefs(pFanin0) == 0 )
        Ivy_ObjDelete_rec( pFanin0, 1 );
    if ( !Ivy_ObjIsNone(pFanin1) && Ivy_ObjRefs(pFanin1) == 0 )
        Ivy_ObjDelete_rec( pFanin1, 1 );
}

/**Function*************************************************************

  Synopsis    [Replaces one object by another.]

  Description [Both objects are currently in the manager. The new object
  (pObjNew) should be used instead of the old object (pObjOld). If the 
  new object is complemented or used, the buffer is added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjReplace( Ivy_Obj_t * pObjOld, Ivy_Obj_t * pObjNew, int fDeleteOld, int fFreeTop )
{
    int nRefsOld;
    // the object to be replaced cannot be complemented
    assert( !Ivy_IsComplement(pObjOld) );
    // the object to be replaced cannot be a terminal
    assert( Ivy_ObjIsNone(pObjOld) || !Ivy_ObjIsTerm(pObjOld) );
    // the object to be used cannot be a PO or assert
    assert( !Ivy_ObjIsPo(Ivy_Regular(pObjNew)) );
    // the object cannot be the same
    assert( pObjOld != Ivy_Regular(pObjNew) );
    // if the new object is complemented or already used, add the buffer
    if ( Ivy_IsComplement(pObjNew) || Ivy_ObjRefs(pObjNew) > 0 || Ivy_ObjIsPi(pObjNew) || Ivy_ObjIsConst1(pObjNew) )
        pObjNew = Ivy_ObjCreate( Ivy_ObjCreateGhost(pObjNew, Ivy_ObjConst1(pObjOld), IVY_BUF, IVY_INIT_NONE) );
    assert( !Ivy_IsComplement(pObjNew) );
    // remember the reference counter
    nRefsOld = pObjOld->nRefs;  
    pObjOld->nRefs = 0;
    // delete the old object
    if ( fDeleteOld )
        Ivy_ObjDelete_rec( pObjOld, fFreeTop );
    // transfer the old object
    assert( Ivy_ObjRefs(pObjNew) == 0 );
    Ivy_ObjOverwrite( pObjOld, pObjNew );
    pObjOld->nRefs = nRefsOld;
    // update the hash table
    Ivy_TableUpdate( pObjNew, pObjOld->Id );
    // create the object that was taken over by pObjOld
    Ivy_ObjClean( pObjNew );
    // remember the entry
    Vec_IntPush( Ivy_ObjMan(pObjOld)->vFree, pObjNew->Id );
}

/**Function*************************************************************

  Synopsis    [Returns the first real fanins (not a buffer/inverter).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_NodeRealFanin_rec( Ivy_Obj_t * pNode, int iFanin )
{
    if ( iFanin == 0 )
    {
        if ( Ivy_ObjIsBuf(Ivy_ObjFanin0(pNode)) )
            return Ivy_NotCond( Ivy_NodeRealFanin_rec(Ivy_ObjFanin0(pNode), 0), Ivy_ObjFaninC0(pNode) );
        else
            return Ivy_ObjChild0(pNode);
    }
    else
    {
        if ( Ivy_ObjIsBuf(Ivy_ObjFanin1(pNode)) )
            return Ivy_NotCond( Ivy_NodeRealFanin_rec(Ivy_ObjFanin1(pNode), 0), Ivy_ObjFaninC1(pNode) );
        else
            return Ivy_ObjChild1(pNode);
    }
}

/**Function*************************************************************

  Synopsis    [Fixes buffer fanins.]

  Description [This situation happens because NodeReplace is a lazy
  procedure, which does not propagate the change to the fanouts but
  instead records the change in the form of a buf/inv node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeFixBufferFanins( Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pFanReal0, * pFanReal1, * pResult;
    assert( Ivy_ObjIsNode(pNode) );
    if ( !Ivy_ObjIsBuf(Ivy_ObjFanin0(pNode)) && !Ivy_ObjIsBuf(Ivy_ObjFanin1(pNode)) )
        return;
    // get the real fanins
    pFanReal0 = Ivy_NodeRealFanin_rec( pNode, 0 );
    pFanReal1 = Ivy_NodeRealFanin_rec( pNode, 1 );
    // get the new node
    pResult = Ivy_Oper( pFanReal0, pFanReal1, Ivy_ObjType(pNode) );
    // perform the replacement
    Ivy_ObjReplace( pNode, pResult, 1, 0 ); 
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


