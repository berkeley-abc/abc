/**CFile****************************************************************

  FileName    [aigFactor.c]

  SystemName  []

  PackageName []

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation []

  Date        [Ver. 1.0. Started - April 17, 2009.]

  Revision    [$Id: aigFactor.c,v 1.00 2009/04/17 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detects multi-input AND gate rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManFindImplications_rec( Aig_Obj_t * pObj, Vec_Ptr_t * vImplics )
{
    if ( Aig_IsComplement(pObj) || Aig_ObjIsPi(pObj) )
    {
        Vec_PtrPushUnique( vImplics, pObj );
        return;
    }
    Aig_ManFindImplications_rec( Aig_ObjChild0(pObj), vImplics );
    Aig_ManFindImplications_rec( Aig_ObjChild1(pObj), vImplics );
}

/**Function*************************************************************

  Synopsis    [Returns the nodes whose values are implied by pNode.]

  Description [Attention!  Both pNode and results can be complemented!
  Also important: Currently, this procedure only does backward propagation. 
  In general, it may find more implications if forward propagation is enabled.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManFindImplications( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    Vec_Ptr_t * vImplics;
    vImplics = Vec_PtrAlloc( 100 );
    Aig_ManFindImplications_rec( pNode, vImplics );
    return vImplics;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the cone of the node overlaps with the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManFindConeOverlap_rec( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    if ( Aig_ObjIsTravIdPrevious( p, pNode ) )
        return 1;
    if ( Aig_ObjIsTravIdCurrent( p, pNode ) )
        return 0;
    Aig_ObjSetTravIdCurrent( p, pNode );
    if ( Aig_ObjIsPi(pNode) )
        return 0;
    if ( Aig_ManFindConeOverlap_rec( p, Aig_ObjFanin0(pNode) ) )
        return 1;
    if ( Aig_ManFindConeOverlap_rec( p, Aig_ObjFanin1(pNode) ) )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the cone of the node overlaps with the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManFindConeOverlap( Aig_Man_t * p, Vec_Ptr_t * vImplics, Aig_Obj_t * pNode )
{
    Aig_Obj_t * pTemp;
    int i;
    assert( !Aig_IsComplement(pNode) );
    assert( !Aig_ObjIsConst1(pNode) );
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vImplics, pTemp, i )
        Aig_ObjSetTravIdCurrent( p, Aig_Regular(pTemp) );
    Aig_ManIncrementTravId( p );
    return Aig_ManFindConeOverlap_rec( p, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the cone of the node overlaps with the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDeriveNewCone_rec( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    if ( Aig_ObjIsTravIdCurrent( p, pNode ) )
        return pNode->pData;
    Aig_ObjSetTravIdCurrent( p, pNode );
    if ( Aig_ObjIsPi(pNode) )
        return pNode->pData = pNode;
    Aig_ManDeriveNewCone_rec( p, Aig_ObjFanin0(pNode) );
    Aig_ManDeriveNewCone_rec( p, Aig_ObjFanin1(pNode) );
    return pNode->pData = Aig_And( p, Aig_ObjChild0Copy(pNode), Aig_ObjChild1Copy(pNode) );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the cone of the node overlaps with the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDeriveNewCone( Aig_Man_t * p, Vec_Ptr_t * vImplics, Aig_Obj_t * pNode )
{
    Aig_Obj_t * pTemp;
    int i;
    assert( !Aig_IsComplement(pNode) );
    assert( !Aig_ObjIsConst1(pNode) );
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vImplics, pTemp, i )
    {
        Aig_ObjSetTravIdCurrent( p, Aig_Regular(pTemp) );
        Aig_Regular(pTemp)->pData = Aig_NotCond( Aig_ManConst1(p), Aig_IsComplement(pTemp) );
    }
    return Aig_ManDeriveNewCone_rec( p, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns algebraic factoring of B in terms of A.]

  Description [Returns internal node C (an AND gate) that is equal to B 
  under assignment A = 'Value', or NULL if there is no such node C. ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManFactorAlgebraic_int( Aig_Man_t * p, Aig_Obj_t * pPoA, Aig_Obj_t * pPoB, int Value )
{
    Aig_Obj_t * pNodeA, * pNodeC;
    Vec_Ptr_t * vImplics;
    int RetValue;
    if ( Aig_ObjIsConst1(Aig_ObjFanin0(pPoA)) || Aig_ObjIsConst1(Aig_ObjFanin0(pPoB)) )
        return NULL;
    if ( Aig_ObjIsPi(Aig_ObjFanin0(pPoB)) )
        return NULL;
    // get the internal node representing function of A under assignment A = 'Value'
    pNodeA = Aig_ObjChild0( pPoA );
    pNodeA = Aig_NotCond( pNodeA, Value==0 );
    // find implications of this signal (nodes whose value is fixed under assignment A = 'Value')
    vImplics = Aig_ManFindImplications( p, pNodeA );
    // check if the TFI cone of B overlaps with the implied nodes
    RetValue = Aig_ManFindConeOverlap( p, vImplics, Aig_ObjFanin0(pPoB) );
    if ( RetValue == 0 ) // no overlap
    {
        Vec_PtrFree( vImplics );
        return NULL;
    }
    // there is overlap - derive node representing value of B under assignment A = 'Value'
    pNodeC = Aig_ManDeriveNewCone( p, vImplics, Aig_ObjFanin0(pPoB) );
    pNodeC = Aig_NotCond( pNodeC, Aig_ObjFaninC0(pPoB) );
    Vec_PtrFree( vImplics );
    return pNodeC;
}

/**Function*************************************************************

  Synopsis    [Returns algebraic factoring of B in terms of A.]

  Description [Returns internal node C (an AND gate) that is equal to B 
  under assignment A = 'Value', or NULL if there is no such node C. ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManFactorAlgebraic( Aig_Man_t * p, int iPoA, int iPoB, int Value )
{
    assert( iPoA >= 0 && iPoA < Aig_ManPoNum(p) );
    assert( iPoB >= 0 && iPoB < Aig_ManPoNum(p) );
    assert( Value == 0 || Value == 1 );
    return Aig_ManFactorAlgebraic_int( p, Aig_ManPo(p, iPoA), Aig_ManPo(p, iPoB), Value ); 
}

/**Function*************************************************************

  Synopsis    [Testing procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManFactorAlgebraicTest( Aig_Man_t * p )
{
    int iPoA  = 0;
    int iPoB  = 1;
    int Value = 0;
    Aig_Obj_t * pRes;
//    Aig_Obj_t * pObj;
//    int i;
    pRes = Aig_ManFactorAlgebraic( p, iPoA, iPoB, Value );
    Aig_ManShow( p, 0, NULL );
    Aig_ObjPrint( p, pRes );
    printf( "\n" );
/*
    printf( "Results:\n" );
    Aig_ManForEachObj( p, pObj, i )
    {
        printf( "Object = %d.\n", i );
        Aig_ObjPrint( p, pObj );
        printf( "\n" );
        Aig_ObjPrint( p, pObj->pData );
        printf( "\n" );
    }
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
