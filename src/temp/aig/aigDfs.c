/**CFile****************************************************************

  FileName    [aigDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [DFS traversal procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aigDfs.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

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
void Aig_ManDfs_rec( Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
        return;
    Aig_ManDfs_rec( Aig_ObjFanin0(pObj), vNodes );
    Aig_ManDfs_rec( Aig_ObjFanin1(pObj), vNodes );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA(pObj);
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManDfs( Aig_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( Aig_ManNodeNum(p) );
    Aig_ManForEachNode( p, pObj, i )
        Aig_ManDfs_rec( pObj, vNodes );
    Aig_ManForEachNode( p, pObj, i )
        Aig_ObjClearMarkA(pObj);
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManDfsNode( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    assert( !Aig_IsComplement(pNode) );
    vNodes = Vec_PtrAlloc( 16 );
    Aig_ManDfs_rec( pNode, vNodes );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Aig_ObjClearMarkA(pObj);
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Computes the max number of levels in the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCountLevels( Aig_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i, LevelsMax, Level0, Level1;
    // initialize the levels
    Aig_ManConst1(p)->pData = NULL;
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = NULL;
    // compute levels in a DFS order
    vNodes = Aig_ManDfs( p );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        Level0 = (int)Aig_ObjFanin0(pObj)->pData;
        Level1 = (int)Aig_ObjFanin1(pObj)->pData;
        pObj->pData = (void *)(1 + Aig_ObjIsExor(pObj) + AIG_MAX(Level0, Level1));
    }
    Vec_PtrFree( vNodes );
    // get levels of the POs
    LevelsMax = 0;
    Aig_ManForEachPo( p, pObj, i )
        LevelsMax = AIG_MAX( LevelsMax, (int)Aig_ObjFanin0(pObj)->pData );
    return LevelsMax;
}

/**Function*************************************************************

  Synopsis    [Creates correct reference counters at each node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCreateRefs( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    if ( p->fRefCount )
        return;
    p->fRefCount = 1;
    // clear refs
    Aig_ObjClearRef( Aig_ManConst1(p) );
    Aig_ManForEachPi( p, pObj, i )
        Aig_ObjClearRef( pObj );
    Aig_ManForEachNode( p, pObj, i )
        Aig_ObjClearRef( pObj );
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjClearRef( pObj );
    // set refs
    Aig_ManForEachNode( p, pObj, i )
    {
        Aig_ObjRef( Aig_ObjFanin0(pObj) );
        Aig_ObjRef( Aig_ObjFanin1(pObj) );
    }
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjRef( Aig_ObjFanin0(pObj) );
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ConeMark_rec( Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
        return;
    Aig_ConeMark_rec( Aig_ObjFanin0(pObj) );
    Aig_ConeMark_rec( Aig_ObjFanin1(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ConeCleanAndMark_rec( Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
        return;
    Aig_ConeCleanAndMark_rec( Aig_ObjFanin0(pObj) );
    Aig_ConeCleanAndMark_rec( Aig_ObjFanin1(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
    pObj->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ConeCountAndMark_rec( Aig_Obj_t * pObj )
{
    int Counter;
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
        return 0;
    Counter = 1 + Aig_ConeCountAndMark_rec( Aig_ObjFanin0(pObj) ) + 
        Aig_ConeCountAndMark_rec( Aig_ObjFanin1(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ConeUnmark_rec( Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || !Aig_ObjIsMarkA(pObj) )
        return;
    Aig_ConeUnmark_rec( Aig_ObjFanin0(pObj) ); 
    Aig_ConeUnmark_rec( Aig_ObjFanin1(pObj) );
    assert( Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjClearMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Counts the number of AIG nodes rooted at this cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_DagSize( Aig_Obj_t * pObj )
{
    int Counter;
    Counter = Aig_ConeCountAndMark_rec( Aig_Regular(pObj) );
    Aig_ConeUnmark_rec( Aig_Regular(pObj) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_Transfer_rec( Aig_Man_t * pDest, Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
        return;
    Aig_Transfer_rec( pDest, Aig_ObjFanin0(pObj) ); 
    Aig_Transfer_rec( pDest, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pDest, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Transfer( Aig_Man_t * pSour, Aig_Man_t * pDest, Aig_Obj_t * pRoot, int nVars )
{
    Aig_Obj_t * pObj;
    int i;
    // solve simple cases
    if ( pSour == pDest )
        return pRoot;
    if ( Aig_ObjIsConst1( Aig_Regular(pRoot) ) )
        return Aig_NotCond( Aig_ManConst1(pDest), Aig_IsComplement(pRoot) );
    // set the PI mapping
    Aig_ManForEachPi( pSour, pObj, i )
    {
        if ( i == nVars )
           break;
        pObj->pData = Aig_IthVar(pDest, i);
    }
    // transfer and set markings
    Aig_Transfer_rec( pDest, Aig_Regular(pRoot) );
    // clear the markings
    Aig_ConeUnmark_rec( Aig_Regular(pRoot) );
    return Aig_NotCond( Aig_Regular(pRoot)->pData, Aig_IsComplement(pRoot) );
}

/**Function*************************************************************

  Synopsis    [Composes the AIG (pRoot) with the function (pFunc) using PI var (iVar).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_Compose_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFunc, Aig_Obj_t * pVar )
{
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsMarkA(pObj) )
        return;
    if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsPi(pObj) )
    {
        pObj->pData = pObj == pVar ? pFunc : pObj;
        return;
    }
    Aig_Compose_rec( p, Aig_ObjFanin0(pObj), pFunc, pVar ); 
    Aig_Compose_rec( p, Aig_ObjFanin1(pObj), pFunc, pVar );
    pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Composes the AIG (pRoot) with the function (pFunc) using PI var (iVar).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Compose( Aig_Man_t * p, Aig_Obj_t * pRoot, Aig_Obj_t * pFunc, int iVar )
{
    // quit if the PI variable is not defined
    if ( iVar >= Aig_ManPiNum(p) )
    {
        printf( "Aig_Compose(): The PI variable %d is not defined.\n", iVar );
        return NULL;
    }
    // recursively perform composition
    Aig_Compose_rec( p, Aig_Regular(pRoot), pFunc, Aig_ManPi(p, iVar) );
    // clear the markings
    Aig_ConeUnmark_rec( Aig_Regular(pRoot) );
    return Aig_NotCond( Aig_Regular(pRoot)->pData, Aig_IsComplement(pRoot) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


