/**CFile****************************************************************

  FileName    [aigDup.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG duplication (re-strashing).]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigDup.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"
#include "tim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupOrdered( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        }
        else if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        }
        else if ( Aig_ObjIsConst1(pObj) )
        {
            pObjNew = Aig_ManConst1(pNew);
        }
        else
            assert( 0 );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupOrdered(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupOrdered(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager to have EXOR gates.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupExor( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->fCatchExor = 1;
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        }
        else if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        }
        else if ( Aig_ObjIsConst1(pObj) )
        {
            pObjNew = Aig_ManConst1(pNew);
        }
        else
            assert( 0 );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    Aig_ManCleanup( pNew );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupExor(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupDfs_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjNew, * pEquivNew = NULL;
    if ( pObj->pData )
        return pObj->pData;
    if ( p->pEquivs && p->pEquivs[pObj->Id] )
        pEquivNew = Aig_ManDupDfs_rec( pNew, p, p->pEquivs[pObj->Id] );
    Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );
    if ( Aig_ObjIsBuf(pObj) )
        return pObj->pData = Aig_ObjChild0Copy(pObj);
    Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin1(pObj) );
    pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
    if ( pObj->pHaig )
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
    if ( pEquivNew )
    {
        if ( pNew->pEquivs )
            pNew->pEquivs[Aig_Regular(pObjNew)->Id] = Aig_Regular(pEquivNew);        
        if ( pNew->pReprs )
            pNew->pReprs[Aig_Regular(pEquivNew)->Id] = Aig_Regular(pObjNew);
    }
    return pObj->pData = pObjNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupDfs( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
    {
        pNew->pEquivs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    if ( p->pReprs )
    {
        pNew->pReprs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );        
//            assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    }
    assert( p->pEquivs != NULL || Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( p->pEquivs == NULL && p->pReprs == NULL && (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupDfs(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupDfs(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManOrderPios( Aig_Man_t * p, Aig_Man_t * pOrder )
{
    Vec_Ptr_t * vPios;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManPiNum(p) == Aig_ManPiNum(pOrder) );
    assert( Aig_ManPoNum(p) == Aig_ManPoNum(pOrder) );
    Aig_ManSetPioNumbers( pOrder );
    vPios = Vec_PtrAlloc( Aig_ManPiNum(p) + Aig_ManPoNum(p) );
    Aig_ManForEachObj( pOrder, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
            Vec_PtrPush( vPios, Aig_ManPi(p, Aig_ObjPioNum(pObj)) );
        else if ( Aig_ObjIsPo(pObj) )
            Vec_PtrPush( vPios, Aig_ManPo(p, Aig_ObjPioNum(pObj)) );
    }
    Aig_ManCleanPioNumbers( pOrder );
    return vPios;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupDfsOrder( Aig_Man_t * p, Aig_Man_t * pOrder )
{
    Vec_Ptr_t * vPios;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
    {
        pNew->pEquivs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    if ( p->pReprs )
    {
        pNew->pReprs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    vPios = Aig_ManOrderPios( p, pOrder );
    Vec_PtrForEachEntry( vPios, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );        
//            assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    }
    Vec_PtrFree( vPios );
//    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( p->pEquivs == NULL && p->pReprs == NULL && (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupDfs(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupDfs(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupLevelized( Aig_Man_t * p )
{
    Vec_Vec_t * vLevels;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, k;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
    {
        pNew->pEquivs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    if ( p->pReprs )
    {
        pNew->pReprs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    // create the PIs
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachPi( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePi( pNew );
        pObjNew->pHaig = pObj->pHaig;
        pObjNew->Level = pObj->Level;
        pObj->pData = pObjNew;
    }
    // duplicate internal nodes
    vLevels = Aig_ManLevelize( p );
    Vec_VecForEachEntry( vLevels, pObj, i, k )
    {
        pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    Vec_VecFree( vLevels );
    // duplicate POs
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        pObjNew->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
//    if ( (nNodes = Aig_ManCleanup( pNew )) )
//        printf( "Aig_ManDupLevelized(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupLevelized(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupWithoutPos( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        assert( !Aig_ObjIsBuf(pObj) );
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


