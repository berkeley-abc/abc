/**CFile****************************************************************

  FileName    [giaDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [DFS procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the support size of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectCis_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vSupp, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCollectCis_rec( p, Gia_ObjFanin0(pObj), vSupp );
    Gia_ManCollectCis_rec( p, Gia_ObjFanin1(pObj), vSupp );
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectCis( Gia_Man_t * p, int * pNodes, int nNodes, Vec_Int_t * vSupp )
{
    Gia_Obj_t * pObj;
    int i; 
    Vec_IntClear( vSupp );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < nNodes; i++ )
    {
        pObj = Gia_ManObj( p, pNodes[i] );
        if ( Gia_ObjIsCo(pObj) )
            Gia_ManCollectCis_rec( p, Gia_ObjFanin0(pObj), vSupp );
        else
            Gia_ManCollectCis_rec( p, pObj, vSupp );
    }
}

/**Function*************************************************************

  Synopsis    [Counts the support size of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectAnds_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vNodes )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCollectAnds_rec( p, Gia_ObjFanin0(pObj), vNodes );
    Gia_ManCollectAnds_rec( p, Gia_ObjFanin1(pObj), vNodes );
    Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectAnds( Gia_Man_t * p, int * pNodes, int nNodes, Vec_Int_t * vNodes )
{
    Gia_Obj_t * pObj;
    int i; 
    Vec_IntClear( vNodes );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < nNodes; i++ )
    {
        pObj = Gia_ManObj( p, pNodes[i] );
        if ( Gia_ObjIsCo(pObj) )
            Gia_ManCollectAnds_rec( p, Gia_ObjFanin0(pObj), vNodes );
        else
            Gia_ManCollectAnds_rec( p, pObj, vNodes );
    }
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManSuppSize_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return 1;
    assert( Gia_ObjIsAnd(pObj) );
    return Gia_ManSuppSize_rec( p, Gia_ObjFanin0(pObj) ) +
        Gia_ManSuppSize_rec( p, Gia_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManSuppSize( Gia_Man_t * p, int * pNodes, int nNodes )
{
    Gia_Obj_t * pObj;
    int i, Counter = 0; 
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < nNodes; i++ )
    {
        pObj = Gia_ManObj( p, pNodes[i] );
        if ( Gia_ObjIsCo(pObj) )
            Counter += Gia_ManSuppSize_rec( p, Gia_ObjFanin0(pObj) );
        else
            Counter += Gia_ManSuppSize_rec( p, pObj );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManConeSize_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    return 1 + Gia_ManConeSize_rec( p, Gia_ObjFanin0(pObj) ) +
        Gia_ManConeSize_rec( p, Gia_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Collects support nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManConeSize( Gia_Man_t * p, int * pNodes, int nNodes )
{
    Gia_Obj_t * pObj;
    int i, Counter = 0; 
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < nNodes; i++ )
    {
        pObj = Gia_ManObj( p, pNodes[i] );
        if ( Gia_ObjIsCo(pObj) )
            Counter += Gia_ManConeSize_rec( p, Gia_ObjFanin0(pObj) );
        else
            Counter += Gia_ManConeSize_rec( p, pObj );
    }
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


