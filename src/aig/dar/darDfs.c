/**CFile****************************************************************

  FileName    [darDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [DFS traversal procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darDfs.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManDfs_rec( Dar_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || Dar_ObjIsMarkA(pObj) )
        return;
    Dar_ManDfs_rec( Dar_ObjFanin0(pObj), vNodes );
    Dar_ManDfs_rec( Dar_ObjFanin1(pObj), vNodes );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA(pObj);
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManDfs( Dar_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( Dar_ManNodeNum(p) );
    Dar_ManForEachObj( p, pObj, i )
        Dar_ManDfs_rec( pObj, vNodes );
    Dar_ManForEachObj( p, pObj, i )
        Dar_ObjClearMarkA(pObj);
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManDfsNode( Dar_Man_t * p, Dar_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i;
    assert( !Dar_IsComplement(pNode) );
    vNodes = Vec_PtrAlloc( 16 );
    Dar_ManDfs_rec( pNode, vNodes );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Dar_ObjClearMarkA(pObj);
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Computes the max number of levels in the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManCountLevels( Dar_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i, LevelsMax, Level0, Level1;
    // initialize the levels
    Dar_ManConst1(p)->pData = NULL;
    Dar_ManForEachPi( p, pObj, i )
        pObj->pData = NULL;
    // compute levels in a DFS order
    vNodes = Dar_ManDfs( p );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        Level0 = (int)Dar_ObjFanin0(pObj)->pData;
        Level1 = (int)Dar_ObjFanin1(pObj)->pData;
        pObj->pData = (void *)(1 + Dar_ObjIsExor(pObj) + DAR_MAX(Level0, Level1));
    }
    Vec_PtrFree( vNodes );
    // get levels of the POs
    LevelsMax = 0;
    Dar_ManForEachPo( p, pObj, i )
        LevelsMax = DAR_MAX( LevelsMax, (int)Dar_ObjFanin0(pObj)->pData );
    return LevelsMax;
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ConeMark_rec( Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || Dar_ObjIsMarkA(pObj) )
        return;
    Dar_ConeMark_rec( Dar_ObjFanin0(pObj) );
    Dar_ConeMark_rec( Dar_ObjFanin1(pObj) );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ConeCleanAndMark_rec( Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || Dar_ObjIsMarkA(pObj) )
        return;
    Dar_ConeCleanAndMark_rec( Dar_ObjFanin0(pObj) );
    Dar_ConeCleanAndMark_rec( Dar_ObjFanin1(pObj) );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA( pObj );
    pObj->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ConeCountAndMark_rec( Dar_Obj_t * pObj )
{
    int Counter;
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || Dar_ObjIsMarkA(pObj) )
        return 0;
    Counter = 1 + Dar_ConeCountAndMark_rec( Dar_ObjFanin0(pObj) ) + 
        Dar_ConeCountAndMark_rec( Dar_ObjFanin1(pObj) );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ConeUnmark_rec( Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || !Dar_ObjIsMarkA(pObj) )
        return;
    Dar_ConeUnmark_rec( Dar_ObjFanin0(pObj) ); 
    Dar_ConeUnmark_rec( Dar_ObjFanin1(pObj) );
    assert( Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjClearMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_DagSize( Dar_Obj_t * pObj )
{
    int Counter;
    Counter = Dar_ConeCountAndMark_rec( Dar_Regular(pObj) );
    Dar_ConeUnmark_rec( Dar_Regular(pObj) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_Transfer_rec( Dar_Man_t * pDest, Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) || Dar_ObjIsMarkA(pObj) )
        return;
    Dar_Transfer_rec( pDest, Dar_ObjFanin0(pObj) ); 
    Dar_Transfer_rec( pDest, Dar_ObjFanin1(pObj) );
    pObj->pData = Dar_And( pDest, Dar_ObjChild0Copy(pObj), Dar_ObjChild1Copy(pObj) );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Transfer( Dar_Man_t * pSour, Dar_Man_t * pDest, Dar_Obj_t * pRoot, int nVars )
{
    Dar_Obj_t * pObj;
    int i;
    // solve simple cases
    if ( pSour == pDest )
        return pRoot;
    if ( Dar_ObjIsConst1( Dar_Regular(pRoot) ) )
        return Dar_NotCond( Dar_ManConst1(pDest), Dar_IsComplement(pRoot) );
    // set the PI mapping
    Dar_ManForEachPi( pSour, pObj, i )
    {
        if ( i == nVars )
           break;
        pObj->pData = Dar_IthVar(pDest, i);
    }
    // transfer and set markings
    Dar_Transfer_rec( pDest, Dar_Regular(pRoot) );
    // clear the markings
    Dar_ConeUnmark_rec( Dar_Regular(pRoot) );
    return Dar_NotCond( Dar_Regular(pRoot)->pData, Dar_IsComplement(pRoot) );
}

/**Function*************************************************************

  Synopsis    [Composes the AIG (pRoot) with the function (pFunc) using PI var (iVar).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_Compose_rec( Dar_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pFunc, Dar_Obj_t * pVar )
{
    assert( !Dar_IsComplement(pObj) );
    if ( Dar_ObjIsMarkA(pObj) )
        return;
    if ( Dar_ObjIsConst1(pObj) || Dar_ObjIsPi(pObj) )
    {
        pObj->pData = pObj == pVar ? pFunc : pObj;
        return;
    }
    Dar_Compose_rec( p, Dar_ObjFanin0(pObj), pFunc, pVar ); 
    Dar_Compose_rec( p, Dar_ObjFanin1(pObj), pFunc, pVar );
    pObj->pData = Dar_And( p, Dar_ObjChild0Copy(pObj), Dar_ObjChild1Copy(pObj) );
    assert( !Dar_ObjIsMarkA(pObj) ); // loop detection
    Dar_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Composes the AIG (pRoot) with the function (pFunc) using PI var (iVar).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Compose( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Obj_t * pFunc, int iVar )
{
    // quit if the PI variable is not defined
    if ( iVar >= Dar_ManPiNum(p) )
    {
        printf( "Dar_Compose(): The PI variable %d is not defined.\n", iVar );
        return NULL;
    }
    // recursively perform composition
    Dar_Compose_rec( p, Dar_Regular(pRoot), pFunc, Dar_ManPi(p, iVar) );
    // clear the markings
    Dar_ConeUnmark_rec( Dar_Regular(pRoot) );
    return Dar_NotCond( Dar_Regular(pRoot)->pData, Dar_IsComplement(pRoot) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


