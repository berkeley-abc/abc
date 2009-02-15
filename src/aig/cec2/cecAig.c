/**CFile****************************************************************

  FileName    [cecAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [AIG manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives combinational miter of the two AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Cec_DeriveMiter_rec( Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return pObj->pData;
    if ( Aig_ObjIsPi(pObj) )
    {
        pObj->pData = Aig_ObjCreatePi( pNew );
        if ( pObj->pHaig )
        {
            assert( pObj->pHaig->pData == NULL );
            pObj->pHaig->pData = pObj->pData;
        }
        return pObj->pData;
    }
    assert( Aig_ObjIsNode(pObj) );
    Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj) );
    Cec_DeriveMiter_rec( pNew, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    return pObj->pData;
}

/**Function*************************************************************

  Synopsis    [Derives combinational miter of the two AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_DeriveMiter( Aig_Man_t * p0, Aig_Man_t * p1 )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj0, * pObj1, * pObjNew;
    int i;
    assert( Aig_ManPiNum(p0) == Aig_ManPiNum(p1) );
    assert( Aig_ManPoNum(p0) == Aig_ManPoNum(p1) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManNodeNum(p0) + Aig_ManNodeNum(p1) );
    pNew->pName = Aig_UtilStrsav( p0->pName );
    // create the PIs
    Aig_ManCleanData( p0 );
    Aig_ManCleanData( p1 );
    Aig_ManConst1(p0)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(p1)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p0, pObj0, i )
    {
        pObj1 = Aig_ManPi( p1, i );
        pObj0->pHaig = pObj1;
        pObj1->pHaig = pObj0;
        if ( Aig_ObjRefs(pObj0) || Aig_ObjRefs(pObj1) )
            continue;
        pObjNew = Aig_ObjCreatePi( pNew );
        pObj0->pData = pObjNew;
        pObj1->pData = pObjNew;
    }
    // add logic for the POs
    pProgress = Bar_ProgressStart( stdout, Aig_ManPoNum(p0) );
    Aig_ManForEachPo( p0, pObj0, i )
    {
        Bar_ProgressUpdate( pProgress, i, "Miter..." );
        pObj1 = Aig_ManPo( p1, i );
        Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj0) );        
        Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj1) );  
        pObjNew = Aig_Exor( pNew, Aig_ObjChild0Copy(pObj0), Aig_ObjChild0Copy(pObj1) );
        Aig_ObjCreatePo( pNew, pObjNew );
    }
    Bar_ProgressStop( pProgress );
    Aig_ManSetRegNum( pNew, 0 );
    assert( Aig_ManHasNoGaps(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_Duplicate( Aig_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // make sure the AIG does not have choices and dangling nodes
    Aig_ManForEachNode( p, pObj, i )
        assert( Aig_ObjRefs(pObj) > 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManNodeNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
    {
        pObj->pHaig = NULL;
        if ( Aig_ObjRefs(pObj) == 0 )
            pObj->pData = Aig_ObjCreatePi( pNew );
    }
    // add logic for the POs
    pProgress = Bar_ProgressStart( stdout, Aig_ManPoNum(p) );
    Aig_ManForEachPo( p, pObj, i )
    {
        Bar_ProgressUpdate( pProgress, i, "Miter..." );
        Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj) );        
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Bar_ProgressStop( pProgress );
    Aig_ManSetRegNum( pNew, 0 );
    assert( Aig_ManHasNoGaps(pNew) );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


