/**CFile****************************************************************

  FileName    [giaCone.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCone.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


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
int Gia_ManConeMark_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vRoots, int nLimit )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsAnd(pObj) )
    {
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin0(pObj), vRoots, nLimit ) )
            return 1;
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin1(pObj), vRoots, nLimit ) )
            return 1;
    }
    else if ( Gia_ObjIsCo(pObj) )
    {
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin0(pObj), vRoots, nLimit ) )
            return 1;
    }
    else if ( Gia_ObjIsRo(p, pObj) )
        Vec_IntPush( vRoots, Gia_ObjId(p, Gia_ObjRoToRi(p, pObj)) );
    else if ( Gia_ObjIsPi(p, pObj) )
    {}
    else assert( 0 );
    return (int)(Vec_IntSize(vRoots) > nLimit);
}
int Gia_ManConeMark( Gia_Man_t * p, int iOut, int Limit )
{
    Vec_Int_t * vRoots;
    Gia_Obj_t * pObj;
    int i, RetValue;
    // start the outputs
    pObj = Gia_ManPo( p, iOut );
    vRoots = Vec_IntAlloc( 100 );
    Vec_IntPush( vRoots, Gia_ObjId(p, pObj) );
    // mark internal nodes
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Gia_ManForEachObjVec( vRoots, p, pObj, i )
        if ( Gia_ManConeMark_rec( p, pObj, vRoots, Limit ) )
            break;
    RetValue = Vec_IntSize( vRoots ) - 1;
    Vec_IntFree( vRoots );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManConeExtract( Gia_Man_t * p, int iOut, int nDelta, int nOutsMin, int nOutsMax )
{
    int i, Count = 0;
    // mark nodes belonging to output 'iOut'
    for ( i = 0; i < Gia_ManPoNum(p); i++ )
        Count += (Gia_ManConeMark(p, i, 10000) < 10000);
     //   printf( "%d ", Gia_ManConeMark(p, i, 1000) );
    printf( "%d out of %d\n", Count, Gia_ManPoNum(p) );

    // add other outputs as long as they are nDelta away

    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

