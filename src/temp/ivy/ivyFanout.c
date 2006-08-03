/**CFile****************************************************************

  FileName    [ivyFanout.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Representation of the fanouts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyFanout.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int          Ivy_FanoutIsArray( void * p )    { return (int )(((unsigned)p) & 01);          }
static inline Vec_Ptr_t *  Ivy_FanoutGetArray( void * p )   { assert( Ivy_FanoutIsArray(p) );  return (Vec_Ptr_t *)((unsigned)(p) & ~01);  }
static inline Vec_Ptr_t *  Ivy_FanoutSetArray( void * p )   { assert( !Ivy_FanoutIsArray(p) ); return (Vec_Ptr_t *)((unsigned)(p) ^  01);  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the fanout representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManStartFanout( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
    assert( p->vFanouts == NULL );
    p->vFanouts = Vec_PtrStart( Ivy_ManObjIdMax(p) + 1000 );
    Ivy_ManForEachObj( p, pObj, i )
    {
        if ( Ivy_ObjFanin0(pObj) )
            Ivy_ObjAddFanout( p, Ivy_ObjFanin0(pObj), pObj );
        if ( Ivy_ObjFanin1(pObj) )
            Ivy_ObjAddFanout( p, Ivy_ObjFanin1(pObj), pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Stops the fanout representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManStopFanout( Ivy_Man_t * p )
{
    void * pTemp;
    int i;
    assert( p->vFanouts != NULL );
    Vec_PtrForEachEntry( p->vFanouts, pTemp, i )
        if ( Ivy_FanoutIsArray(pTemp) )
            Vec_PtrFree( Ivy_FanoutGetArray(pTemp) );
    Vec_PtrFree( p->vFanouts );
    p->vFanouts = NULL;
}

/**Function*************************************************************

  Synopsis    [Add the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjAddFanout( Ivy_Man_t * p, Ivy_Obj_t * pObj, Ivy_Obj_t * pFanout )
{
    Vec_Ptr_t * vNodes;
    void ** ppSpot;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    // get the pointer to the place where fanouts are stored
    ppSpot = Vec_PtrEntryP( p->vFanouts, pObj->Id );
    // consider several cases
    if ( *ppSpot == NULL ) // no fanout - add one fanout
        *ppSpot = pFanout;
    else if ( Ivy_FanoutIsArray(*ppSpot) ) // array of fanouts - add one fanout
    {
        vNodes = Ivy_FanoutGetArray(*ppSpot);
        Vec_PtrPush( vNodes, pFanout );
    }
    else // only one fanout - create array and put both fanouts into the array
    {
        vNodes = Vec_PtrAlloc( 4 );
        Vec_PtrPush( vNodes, *ppSpot );
        Vec_PtrPush( vNodes, pFanout );
        *ppSpot = Ivy_FanoutSetArray( vNodes );
    }
}

/**Function*************************************************************

  Synopsis    [Removes the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjDeleteFanout( Ivy_Man_t * p, Ivy_Obj_t * pObj, Ivy_Obj_t * pFanout )
{
    Vec_Ptr_t * vNodes;
    void ** ppSpot;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    ppSpot = Vec_PtrEntryP( p->vFanouts, pObj->Id );
    if ( *ppSpot == NULL ) // no fanout - should not happen
    {
        assert( 0 );
    }
    else if ( Ivy_FanoutIsArray(*ppSpot) ) // the array of fanouts - delete the fanout
    {
        vNodes = Ivy_FanoutGetArray(*ppSpot);
        Vec_PtrRemove( vNodes, pFanout );
    }
    else // only one fanout - delete the fanout
    {
        assert( *ppSpot == pFanout );
        *ppSpot = NULL;
    }
//    printf( " %d", Ivy_ObjFanoutNum(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Replaces the fanout of pOld to be pFanoutNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjPatchFanout( Ivy_Man_t * p, Ivy_Obj_t * pObj, Ivy_Obj_t * pFanoutOld, Ivy_Obj_t * pFanoutNew )
{
    Vec_Ptr_t * vNodes;
    void ** ppSpot;
    int Index;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    ppSpot = Vec_PtrEntryP( p->vFanouts, pObj->Id );
    if ( *ppSpot == NULL ) // no fanout - should not happen
    {
        assert( 0 );
    }
    else if ( Ivy_FanoutIsArray(*ppSpot) ) // the array of fanouts - find and replace the fanout
    {
        vNodes = Ivy_FanoutGetArray(*ppSpot);
        Index = Vec_PtrFind( vNodes, pFanoutOld );
        assert( Index >= 0 );
        Vec_PtrWriteEntry( vNodes, Index, pFanoutNew );
    }
    else // only one fanout - delete the fanout
    {
        assert( *ppSpot == pFanoutOld );
        *ppSpot = pFanoutNew;
    }
}

/**Function*************************************************************

  Synopsis    [Starts iteration through the fanouts.]

  Description [Copies the currently available fanouts into the array.]
               
  SideEffects [Can be used while the fanouts are being removed.]

  SeeAlso     []

***********************************************************************/
void Ivy_ObjCollectFanouts( Ivy_Man_t * p, Ivy_Obj_t * pObj, Vec_Ptr_t * vArray )
{
    Vec_Ptr_t * vNodes;
    Ivy_Obj_t * pTemp;
    int i;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    vNodes = Vec_PtrEntry( p->vFanouts, pObj->Id );
    // clean the resulting array
    Vec_PtrClear( vArray );
    if ( vNodes == NULL ) // no fanout - nothing to do
    {
    }
    else if ( Ivy_FanoutIsArray(vNodes) ) // the array of fanouts - copy fanouts
    {
        vNodes = Ivy_FanoutGetArray(vNodes);
        Vec_PtrForEachEntry( vNodes, pTemp, i )
            Vec_PtrPush( vArray, pTemp );
    }
    else // only one fanout - add the fanout
        Vec_PtrPush( vArray, vNodes );
}

/**Function*************************************************************

  Synopsis    [Reads one fanout.]

  Description [Returns fanout if there is only one fanout.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjReadOneFanout( Ivy_Man_t * p, Ivy_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    vNodes = Vec_PtrEntry( p->vFanouts, pObj->Id );
    // clean the resulting array
    if ( vNodes && !Ivy_FanoutIsArray(vNodes) ) // only one fanout - return
        return (Ivy_Obj_t *)vNodes;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Reads one fanout.]

  Description [Returns fanout if there is only one fanout.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjReadFirstFanout( Ivy_Man_t * p, Ivy_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    vNodes = Vec_PtrEntry( p->vFanouts, pObj->Id );
    // clean the resulting array
    if ( vNodes == NULL )
        return NULL;
    if ( !Ivy_FanoutIsArray(vNodes) ) // only one fanout - return
        return (Ivy_Obj_t *)vNodes;
    return Vec_PtrEntry( Ivy_FanoutGetArray(vNodes), 0 );
}

/**Function*************************************************************

  Synopsis    [Reads one fanout.]

  Description [Returns fanout if there is only one fanout.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ObjFanoutNum( Ivy_Man_t * p, Ivy_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes;
    assert( p->vFanouts != NULL );
    assert( !Ivy_IsComplement(pObj) );
    // extend the fanout array if needed
    Vec_PtrFillExtra( p->vFanouts, pObj->Id + 1, NULL );
    vNodes = Vec_PtrEntry( p->vFanouts, pObj->Id );
    // clean the resulting array
    if ( vNodes == NULL )
        return 0;
    if ( !Ivy_FanoutIsArray(vNodes) ) // only one fanout - return
        return 1;
    return Vec_PtrSize( Ivy_FanoutGetArray(vNodes) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


