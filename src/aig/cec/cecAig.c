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
    Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj) );
    if ( Aig_ObjIsBuf(pObj) )
        return pObj->pData = Aig_ObjChild0Copy(pObj);
    Cec_DeriveMiter_rec( pNew, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_Regular(pObj->pData)->pHaig = pObj->pHaig;
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
        pObjNew = Aig_ObjCreatePi( pNew );
        pObj0->pData = pObjNew;
        Aig_ManPi(p1, i)->pData = pObjNew;
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
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, 0 );
    // check the resulting network
//    if ( !Aig_ManCheck(pNew) )
//        printf( "Cec_DeriveMiter(): The check has failed.\n" );
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
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManNodeNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // add logic for the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        Cec_DeriveMiter_rec( pNew, Aig_ObjFanin0(pObj) );        
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, 0 );
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    // check the resulting network
//    if ( !Aig_ManCheck(pNew) )
//        printf( "Cec_DeriveMiter(): The check has failed.\n" );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


