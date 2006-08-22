/**CFile****************************************************************

  FileName    [abcObj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Object creation/duplication/deletion procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcObj.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "abcInt.h"
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_ObjAlloc( Abc_Ntk_t * pNtk, Abc_ObjType_t Type )
{
    Abc_Obj_t * pObj;
    pObj = (Abc_Obj_t *)Extra_MmFixedEntryFetch( pNtk->pMmObj );
    memset( pObj, 0, sizeof(Abc_Obj_t) );
    pObj->pNtk = pNtk;
    pObj->Type = Type;
    pObj->Id   = -1;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Recycles the Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjRecycle( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    int LargePiece = (4 << ABC_NUM_STEPS);
    // free large fanout arrays
    if ( pObj->vFanouts.nCap * 4 > LargePiece )
        FREE( pObj->vFanouts.pArray );
    // clean the memory to make deleted object distinct from the live one
    memset( pObj, 0, sizeof(Abc_Obj_t) );
    // recycle the object
    Extra_MmFixedEntryRecycle( pNtk->pMmObj, (char *)pObj );
}

/**Function*************************************************************

  Synopsis    [Adds the node to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjAdd( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    assert( !Abc_ObjIsComplement(pObj) );
    // add to the array of objects
    pObj->Id = pNtk->vObjs->nSize;
    Vec_PtrPush( pNtk->vObjs, pObj );
    pNtk->nObjs++;
    // perform specialized operations depending on the object type
    if ( Abc_ObjIsNode(pObj) )
    {
        pNtk->nNodes++;
    }
    else if ( Abc_ObjIsNet(pObj) )
    {
        pNtk->nNets++;
    }
    else if ( Abc_ObjIsPi(pObj) )
    {
        Vec_PtrPush( pNtk->vPis, pObj );
        Vec_PtrPush( pNtk->vCis, pObj );
    }
    else if ( Abc_ObjIsPo(pObj) )
    {
        Vec_PtrPush( pNtk->vPos, pObj );
        Vec_PtrPush( pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        Vec_PtrPush( pNtk->vLatches, pObj );
        Vec_PtrPush( pNtk->vCis, pObj );
        Vec_PtrPush( pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsAssert(pObj) )
    {
        Vec_PtrPush( pNtk->vAsserts, pObj );
        Vec_PtrPush( pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsBi(pObj) )
    {
        Vec_PtrPush( pNtk->vCis, pObj );
    }
    else if ( Abc_ObjIsBo(pObj) )
    {
        Vec_PtrPush( pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsBox(pObj) )
    {
        pNtk->nBoxes++;
        Vec_PtrPush( pNtk->vBoxes, pObj );
    }
    else assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Duplicate the Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupObj( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pObjNew;
    // create the new object
    pObjNew = Abc_ObjAlloc( pNtkNew, pObj->Type );
    // add the object to the network
    Abc_ObjAdd( pObjNew );
    // copy functionality/names
    if ( Abc_ObjIsNode(pObj) ) // copy the function if functionality is compatible
    {
        if ( pNtkNew->ntkFunc == pObj->pNtk->ntkFunc ) 
        {
            if ( Abc_NtkIsStrash(pNtkNew) || Abc_NtkIsSeq(pNtkNew) ) 
            {}
            else if ( Abc_NtkHasSop(pNtkNew) )
                pObjNew->pData = Abc_SopRegister( pNtkNew->pManFunc, pObj->pData );
            else if ( Abc_NtkHasBdd(pNtkNew) )
                pObjNew->pData = Cudd_bddTransfer(pObj->pNtk->pManFunc, pNtkNew->pManFunc, pObj->pData), Cudd_Ref(pObjNew->pData);
            else if ( Abc_NtkHasAig(pNtkNew) )
                pObjNew->pData = Aig_Transfer(pObj->pNtk->pManFunc, pNtkNew->pManFunc, pObj->pData, Abc_ObjFaninNum(pObj));
            else if ( Abc_NtkHasMapping(pNtkNew) )
                pObjNew->pData = pObj->pData;
            else assert( 0 );
        }
    }
    else if ( Abc_ObjIsNet(pObj) ) // copy the name
    {
        pObjNew->pData = Nm_ManStoreIdName( pNtkNew->pManName, pObjNew->Id, pObj->pData, NULL );
    }
    else if ( Abc_ObjIsLatch(pObj) ) // copy the reset value
        pObjNew->pData = pObj->pData;
    pObj->pCopy = pObjNew;
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Clones the objects in the same network but does not assign its function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCloneObj( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pClone, * pFanin;
    int i;
    pClone = Abc_ObjAlloc( pObj->pNtk, pObj->Type );   
    Abc_ObjAdd( pClone );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_ObjAddFanin( pClone, pFanin );
    return pClone;
}

/**Function*************************************************************

  Synopsis    [Deletes the object from the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDeleteObj( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    Vec_Ptr_t * vNodes;
    int i;

    assert( !Abc_ObjIsComplement(pObj) );

    // delete fanins and fanouts
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NodeCollectFanouts( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( vNodes->pArray[i], pObj );
    Abc_NodeCollectFanins( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( pObj, vNodes->pArray[i] );
    Vec_PtrFree( vNodes );

    // remove from the list of objects
    Vec_PtrWriteEntry( pNtk->vObjs, pObj->Id, NULL );
    pObj->Id = (1<<26)-1;
    pNtk->nObjs--;

    // remove from the table of names
    if ( Nm_ManFindNameById(pObj->pNtk->pManName, pObj->Id) )
        Nm_ManDeleteIdName(pObj->pNtk->pManName, pObj->Id);

    // perform specialized operations depending on the object type
    if ( Abc_ObjIsNet(pObj) )
    {
        pObj->pData = NULL;
        pNtk->nNets--;
    }
    else if ( Abc_ObjIsNode(pObj) )
    {
        if ( Abc_NtkHasBdd(pNtk) )
            Cudd_RecursiveDeref( pNtk->pManFunc, pObj->pData );
        pObj->pData = NULL;
        pNtk->nNodes--;
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        Vec_PtrRemove( pNtk->vLatches, pObj );
        Vec_PtrRemove( pNtk->vCis, pObj );
        Vec_PtrRemove( pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsPi(pObj) )
    {
        Vec_PtrRemove( pObj->pNtk->vPis, pObj );
        Vec_PtrRemove( pObj->pNtk->vCis, pObj );
    }
    else if ( Abc_ObjIsPo(pObj) )
    {
        Vec_PtrRemove( pObj->pNtk->vPos, pObj );
        Vec_PtrRemove( pObj->pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsBi(pObj) )
    {
        Vec_PtrRemove( pObj->pNtk->vCis, pObj );
    }
    else if ( Abc_ObjIsBo(pObj) )
    {
        Vec_PtrRemove( pObj->pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsAssert(pObj) )
    {
        Vec_PtrRemove( pObj->pNtk->vAsserts, pObj );
        Vec_PtrRemove( pObj->pNtk->vCos, pObj );
    }
    else if ( Abc_ObjIsBox(pObj) )
    {
        pNtk->nBoxes--;
        Vec_PtrRemove( pObj->pNtk->vBoxes, pObj );
    }
    else
        assert( 0 );
    // recycle the net itself
    Abc_ObjRecycle( pObj );
}

/**Function*************************************************************

  Synopsis    [Deletes the node and MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDeleteObj_rec( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    Vec_Ptr_t * vNodes;
    int i;
    assert( !Abc_ObjIsComplement(pObj) );
    assert( Abc_ObjFanoutNum(pObj) == 0 );
    // delete fanins and fanouts
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NodeCollectFanins( pObj, vNodes );
    Abc_NtkDeleteObj( pObj );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Abc_ObjIsNode(pObj) && Abc_ObjFanoutNum(pObj) == 0 )
            Abc_NtkDeleteObj_rec( pObj );
    Vec_PtrFree( vNodes );
}


/**Function*************************************************************

  Synopsis    [Returns the net with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindNode( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pObj, * pDriver;
    int i, Num;
    // check if the node is among CIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( strcmp( Abc_ObjName(pObj), pName ) == 0 )
        {
            if ( i < Abc_NtkPiNum(pNtk) )
                printf( "Node \"%s\" is a primary input.\n", pName );
            else
                printf( "Node \"%s\" is a latch output.\n", pName );
            return NULL;
        }
    }
    // search the node among COs
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        if ( strcmp( Abc_ObjName(pObj), pName ) == 0 )
        {
            pDriver = Abc_ObjFanin0(pObj);
            if ( !Abc_ObjIsNode(pDriver) )
            {
                printf( "Node \"%s\" does not have logic associated with it.\n", pName );
                return NULL;
            }
            return pDriver;
        }
    }
    // find the internal node
    if ( pName[0] != '[' || pName[strlen(pName)-1] != ']' )
    {
        printf( "Name \"%s\" is not found among CIs/COs (internal name looks like this: \"[integer]\").\n", pName );
        return NULL;
    }
    Num = atoi( pName + 1 );
    if ( Num < 0 || Num >= Abc_NtkObjNumMax(pNtk) )
    {
        printf( "The node \"%s\" with ID %d is not in the current network.\n", pName, Num );
        return NULL;
    }
    pObj = Abc_NtkObj( pNtk, Num );
    if ( pObj == NULL )
    {
        printf( "The node \"%s\" with ID %d has been removed from the current network.\n", pName, Num );
        return NULL;
    }
    if ( !Abc_ObjIsNode(pObj) )
    {
        printf( "Object with ID %d is not a node.\n", Num );
        return NULL;
    }
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Returns the net with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindNet( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet;
    int ObjId;
    assert( Abc_NtkIsNetlist(pNtk) );
    ObjId = Nm_ManFindIdByName( pNtk->pManName, pName, NULL );
    if ( ObjId == -1 )
        return NULL;
    pNet = Abc_NtkObj( pNtk, ObjId );
    return pNet;
}

/**Function*************************************************************

  Synopsis    [Returns the CI/CO terminal with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindTerm( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet;
    int ObjId;
    assert( !Abc_NtkIsNetlist(pNtk) );
    ObjId = Nm_ManFindIdByName( pNtk->pManName, pName, NULL );
    if ( ObjId == -1 )
        return NULL;
    pNet = Abc_NtkObj( pNtk, ObjId );
    return pNet;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindOrCreateNet( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet;
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( pNet = Abc_NtkFindNet( pNtk, pName ) )
        return pNet;
    // create a new net
    pNet = Abc_ObjAlloc( pNtk, ABC_OBJ_NET );
    Abc_ObjAdd( pNet );
    pNet->pData = Nm_ManStoreIdName( pNtk->pManName, pNet->Id, pName, NULL );
    return pNet;
}
    
/**Function*************************************************************

  Synopsis    [Create node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateNode( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_NODE );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Create multi-input/multi-output box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateBox( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_BOX );     
    Abc_ObjAdd( pObj );
    return pObj;
}
    
/**Function*************************************************************

  Synopsis    [Create primary input.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreatePi( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_PI );     
    Abc_ObjAdd( pObj );
    return pObj;
}
    
/**Function*************************************************************

  Synopsis    [Create primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreatePo( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_PO );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates latch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateLatch( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_LATCH );     
    pObj->pData = (void *)ABC_INIT_NONE;
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates assert.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateAssert( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_ASSERT );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates constant 0 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst0( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 0\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_ReadLogicZero(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_ManConst0(pNtk->pManFunc);
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadConst0(Abc_FrameReadLibGen());
    else if ( !Abc_NtkHasBlackbox(pNtk) )
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst1( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_ReadOne(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_ManConst1(pNtk->pManFunc);
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadConst1(Abc_FrameReadLibGen());
    else if ( !Abc_NtkHasBlackbox(pNtk) )
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pFanin );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "0 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_Not(Cudd_bddIthVar(pNtk->pManFunc,0)), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_Not(Aig_IthVar(pNtk->pManFunc,0));
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadInv(Abc_FrameReadLibGen());
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates buffer.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateBuf( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pFanin );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "1 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_bddIthVar(pNtk->pManFunc,0), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_IthVar(pNtk->pManFunc,0);
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadBuf(Abc_FrameReadLibGen());
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates AND.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateAnd( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopCreateAnd( pNtk->pManFunc, Vec_PtrSize(vFanins), NULL );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Extra_bddCreateAnd( pNtk->pManFunc, Vec_PtrSize(vFanins) ), Cudd_Ref(pNode->pData); 
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_CreateAnd( pNtk->pManFunc, Vec_PtrSize(vFanins) ); 
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates OR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateOr( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopCreateOr( pNtk->pManFunc, Vec_PtrSize(vFanins), NULL );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Extra_bddCreateOr( pNtk->pManFunc, Vec_PtrSize(vFanins) ), Cudd_Ref(pNode->pData); 
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_CreateOr( pNtk->pManFunc, Vec_PtrSize(vFanins) ); 
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates EXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateExor( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopCreateXorSpecial( pNtk->pManFunc, Vec_PtrSize(vFanins) );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Extra_bddCreateExor( pNtk->pManFunc, Vec_PtrSize(vFanins) ), Cudd_Ref(pNode->pData); 
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_CreateExor( pNtk->pManFunc, Vec_PtrSize(vFanins) ); 
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates MUX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateMux( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodeC, Abc_Obj_t * pNode1, Abc_Obj_t * pNode0 )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pNodeC );
    Abc_ObjAddFanin( pNode, pNode1 );
    Abc_ObjAddFanin( pNode, pNode0 );
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "11- 1\n0-1 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_bddIte(pNtk->pManFunc,Cudd_bddIthVar(pNtk->pManFunc,0),Cudd_bddIthVar(pNtk->pManFunc,1),Cudd_bddIthVar(pNtk->pManFunc,2)), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pNode->pData = Aig_Mux(pNtk->pManFunc,Aig_IthVar(pNtk->pManFunc,0),Aig_IthVar(pNtk->pManFunc,1),Aig_IthVar(pNtk->pManFunc,2));
    else
        assert( 0 );
    return pNode;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if the node is a constant 0 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst( Abc_Obj_t * pNode )    
{ 
    assert( Abc_NtkIsLogic(pNode->pNtk) || Abc_NtkIsNetlist(pNode->pNtk) );
    assert( Abc_ObjIsNode(pNode) );      
    return Abc_ObjFaninNum(pNode) == 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is a constant 0 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst0( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    assert( Abc_ObjIsNode(pNode) );      
    if ( !Abc_NodeIsConst(pNode) )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsConst0(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return Aig_IsComplement(pNode->pData);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadConst0(Abc_FrameReadLibGen());
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is a constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst1( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    assert( Abc_ObjIsNode(pNode) );      
    if ( !Abc_NodeIsConst(pNode) )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsConst1(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return !Aig_IsComplement(pNode->pData);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadConst1(Abc_FrameReadLibGen());
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is a buffer.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsBuf( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    assert( Abc_ObjIsNode(pNode) ); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsBuf(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return !Aig_IsComplement(pNode->pData);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadBuf(Abc_FrameReadLibGen());
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is an inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsInv( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    assert( Abc_ObjIsNode(pNode) ); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsInv(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return Aig_IsComplement(pNode->pData);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadInv(Abc_FrameReadLibGen());
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Complements the local functions of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeComplement( Abc_Obj_t * pNode )
{
    assert( Abc_NtkIsLogic(pNode->pNtk) || Abc_NtkIsNetlist(pNode->pNtk) );
    assert( Abc_ObjIsNode(pNode) ); 
    if ( Abc_NtkHasSop(pNode->pNtk) )
        Abc_SopComplement( pNode->pData );
    else if ( Abc_NtkHasBdd(pNode->pNtk) )
        pNode->pData = Cudd_Not( pNode->pData );
    else if ( Abc_NtkHasAig(pNode->pNtk) )
        pNode->pData = Aig_Not( pNode->pData );
    else
        assert( 0 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

