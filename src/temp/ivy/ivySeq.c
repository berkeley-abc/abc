/**CFile****************************************************************

  FileName    [ivySeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivySeq.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts a combinational AIG manager into a sequential one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManMakeSeq( Ivy_Man_t * p, int nLatches )
{
    Vec_Int_t * vNodes;
    Ivy_Obj_t * pObj, * pObjNew, * pFan0, * pFan1;
    int i, fChanges;
    assert( nLatches < Ivy_ManPiNum(p) && nLatches < Ivy_ManPoNum(p) );
    // change POs into buffers
    assert( Ivy_ManPoNum(p) == Vec_IntSize(p->vPos) );
    for ( i = Ivy_ManPoNum(p) - nLatches; i < Vec_IntSize(p->vPos); i++ )
    {
        pObj = Ivy_ManPo(p, i);
        pObj->Type = IVY_BUF;
    }
    // change PIs into latches and connect them to the corresponding POs
    assert( Ivy_ManPiNum(p) == Vec_IntSize(p->vPis) );
    for ( i = Ivy_ManPiNum(p) - nLatches; i < Vec_IntSize(p->vPis); i++ )
    {
        pObj = Ivy_ManPi(p, i);
        pObj->Type = IVY_LATCH;
        Ivy_ObjConnect( pObj, Ivy_ManPo(p, Ivy_ManPoNum(p) - Ivy_ManPiNum(p)) );
    }
    // shrink the array
    Vec_IntShrink( p->vPis, Ivy_ManPiNum(p) - nLatches );
    Vec_IntShrink( p->vPos, Ivy_ManPoNum(p) - nLatches );
    // update the counters of different objects
    p->nObjs[IVY_PI] -= nLatches;
    p->nObjs[IVY_PO] -= nLatches;
    p->nObjs[IVY_BUF] += nLatches;
    p->nObjs[IVY_LATCH] += nLatches;
    // perform structural hashing while there are changes
    fChanges = 1;
    while ( fChanges )
    {
        fChanges = 0;
        vNodes = Ivy_ManDfs( p );
        Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
        {
            if ( Ivy_ObjIsBuf(pObj) )
                continue;
            pFan0 = Ivy_NodeRealFanin_rec( pObj, 0 );
            pFan1 = Ivy_NodeRealFanin_rec( pObj, 1 );
            if ( Ivy_ObjIsAnd(pObj) )
                pObjNew = Ivy_And(pFan0, pFan1);
            else if ( Ivy_ObjIsExor(pObj) )
                pObjNew = Ivy_Exor(pFan0, pFan1);
            else assert( 0 );
            if ( pObjNew == pObj )
                continue;
            Ivy_ObjReplace( pObj, pObjNew, 1, 1 );
            fChanges = 1;
        }
        Vec_IntFree( vNodes );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


