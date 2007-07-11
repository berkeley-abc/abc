/**CFile****************************************************************

  FileName    [cswCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cut sweeping.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 11, 2007.]

  Revision    [$Id: cswCore.c,v 1.00 2007/07/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cswInt.h"

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
Dar_Man_t * Csw_Sweep( Dar_Man_t * pAig, int nCutsMax, int nLeafMax, int fVerbose )
{
    Csw_Man_t * p;
    Dar_Man_t * pRes;
    Dar_Obj_t * pObj, * pObjNew, * pObjRes;
    int i;
    // start the manager
    p = Csw_ManStart( pAig, nCutsMax, nLeafMax, fVerbose );
    // set elementary cuts at the PIs
    Dar_ManForEachPi( p->pManRes, pObj, i )
        Csw_ObjPrepareCuts( p, pObj, 1 );
    // process the nodes
    Dar_ManForEachNode( pAig, pObj, i )
    {
        // create the new node
        pObjNew = Dar_And( p->pManRes, Csw_ObjChild0Equiv(p, pObj), Csw_ObjChild1Equiv(p, pObj) );
        // check if this node can be represented using another node
        pObjRes = Csw_ObjSweep( p, Dar_Regular(pObjNew), pObj->nRefs > 1 );
        pObjRes = Dar_NotCond( pObjRes, Dar_IsComplement(pObjNew) );
        // set the resulting node
        Csw_ObjSetEquiv( p, pObj, pObjRes );
    }
    // add the POs
    Dar_ManForEachPo( pAig, pObj, i )
        Dar_ObjCreatePo( p->pManRes, Csw_ObjChild0Equiv(p, pObj) );
    // remove dangling nodes 
    Dar_ManCleanup( p->pManRes );
    // return the resulting manager
    pRes = p->pManRes;
    Csw_ManStop( p );
    return pRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


