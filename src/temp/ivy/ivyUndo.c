/**CFile****************************************************************

  FileName    [ivyUndo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Recording the results of recent deletion of logic cone.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyUndo.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManUndoStart( Ivy_Man_t * p )
{
    p->fRecording = 1;
    p->nUndos = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManUndoStop( Ivy_Man_t * p )
{
    p->fRecording = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManUndoRecord( Ivy_Man_t * p, Ivy_Obj_t * pObj )
{
    Ivy_Obj_t * pObjUndo;
    if ( p->nUndos >= p->nUndosAlloc )
    {
        printf( "Ivy_ManUndoRecord(): Not enough memory for undo.\n" );
        return;
    }
    pObjUndo = p->pUndos + p->nUndos++;
    // required data for Ivy_ObjCreateGhost()
    pObjUndo->Type    = pObj->Type;
    pObjUndo->Init    = pObj->Init;
    pObjUndo->Fanin0  = pObj->Fanin0;
    pObjUndo->Fanin1  = pObj->Fanin1;
    pObjUndo->fComp0  = pObj->fComp0;
    pObjUndo->fComp1  = pObj->fComp1;
    // additional data
    pObjUndo->Id      = pObj->Id;
    pObjUndo->nRefs   = pObj->nRefs;
    pObjUndo->Level   = pObj->Level;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vec_IntPutLast( Vec_Int_t * vFree, int Last )
{
    int Place, i;
    // find the entry
    Place = Vec_IntFind( vFree, Last );
    if ( Place == -1 )
        return 0;
    // shift entries by one
    assert( vFree->pArray[Place] == Last );
    for ( i = Place; i < Vec_IntSize(vFree) - 1; i++ )
        vFree->pArray[i] = vFree->pArray[i+1];
    // put the entry in the end
    vFree->pArray[i] = Last;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManUndoPerform( Ivy_Man_t * p, Ivy_Obj_t * pRoot )
{
    Ivy_Obj_t * pObjUndo, * pObjNew;
    int i;
    assert( p->nUndos > 0 );
    assert( p->fRecording == 0 );
    for ( i = p->nUndos - 1; i >= 0; i-- )
    {
        // get the undo object
        pObjUndo = p->pUndos + i;
        // if this is the last object
        if ( i == 0 )
            Vec_IntPush( p->vFree, pRoot->Id );
        else
            Vec_IntPutLast( p->vFree, pObjUndo->Id );
        // create the new object
        pObjNew  = Ivy_ObjCreate( Ivy_ObjCreateGhost2( p, pObjUndo) );
        pObjNew->nRefs = pObjUndo->nRefs;
        pObjNew->Level = pObjUndo->Level;
        // make sure the object is created in the same place as before
        assert( pObjNew->Id == pObjUndo->Id );
    }
    p->nUndos = 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


