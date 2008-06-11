/**CFile****************************************************************

  FileName    [saigMiter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Computes sequential miter of two sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigMiter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

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
Aig_Man_t * Saig_ManCreateMiter( Aig_Man_t * p1, Aig_Man_t * p2, int Oper )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Saig_ManRegNum(p1) > 0 || Saig_ManRegNum(p2) > 0 );
    assert( Saig_ManPiNum(p1) == Saig_ManPiNum(p2) );
    assert( Saig_ManPoNum(p1) == Saig_ManPoNum(p2) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p1) + Aig_ManObjNumMax(p2) );
    // map constant nodes
    Aig_ManConst1(p1)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(p2)->pData = Aig_ManConst1(pNew);
    // map primary inputs
    Saig_ManForEachPi( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Saig_ManForEachPi( p2, pObj, i )
        pObj->pData = Aig_ManPi( pNew, i );
    // map register outputs
    Saig_ManForEachLo( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Saig_ManForEachLo( p2, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // map internal nodes
    Aig_ManForEachNode( p1, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachNode( p2, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create primary outputs
    Saig_ManForEachPo( p1, pObj, i )
    {
        if ( Oper == 0 ) // XOR
            pObj = Aig_Exor( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild0Copy(Aig_ManPo(p2,i)) );
        else if ( Oper == 1 ) // implication is PO(p1) -> PO(p2)  ...  complement is PO(p1) & !PO(p2) 
            pObj = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_Not(Aig_ObjChild0Copy(Aig_ManPo(p2,i))) );
        else
            assert( 0 );
        Aig_ObjCreatePo( pNew, pObj );
    }
    // create register inputs
    Saig_ManForEachLi( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Saig_ManForEachLi( p2, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // cleanup
    Aig_ManSetRegNum( pNew, Saig_ManRegNum(p1) + Saig_ManRegNum(p2) );
    Aig_ManCleanup( pNew );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


