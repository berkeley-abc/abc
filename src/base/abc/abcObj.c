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
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
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
    pObj->Id   = -1;
    pObj->pNtk = pNtk;
    pObj->Type = Type;
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
    memset( pObj, 0, sizeof(Abc_Obj_t) );
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
    if ( Abc_ObjIsNet(pObj) )
    {
        // add the name to the table
        if ( pObj->pData && stmm_insert( pNtk->tName2Net, pObj->pData, (char *)pObj ) )
        {
            printf( "Error: The net is already in the table...\n" );
            assert( 0 );
        }
        pNtk->nNets++;
    }
    else if ( Abc_ObjIsNode(pObj) )
    {
        pNtk->nNodes++;
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        Vec_PtrPush( pNtk->vLats, pObj );
        pNtk->nLatches++;
    }
    else if ( Abc_ObjIsPi(pObj) )
    {
        Vec_PtrPush( pNtk->vCis, pObj );
        pNtk->nPis++;
    }
    else if ( Abc_ObjIsPo(pObj) )
    {
        Vec_PtrPush( pNtk->vCos, pObj );
        pNtk->nPos++;
    }
    else
    {
        assert( 0 );
    }
    assert( pObj->Id >= 0 );
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
    pObjNew = Abc_ObjAlloc( pNtkNew, pObj->Type );
    if ( Abc_ObjIsNode(pObj) ) // copy the function if functionality is compatible
    {
        if ( pNtkNew->ntkFunc == pObj->pNtk->ntkFunc ) 
        {
            if ( Abc_NtkHasSop(pNtkNew) )
                pObjNew->pData = Abc_SopRegister( pNtkNew->pManFunc, pObj->pData );
            else if ( Abc_NtkHasBdd(pNtkNew) )
                pObjNew->pData = Cudd_bddTransfer(pObj->pNtk->pManFunc, pNtkNew->pManFunc, pObj->pData), Cudd_Ref(pObjNew->pData);
            else if ( Abc_NtkHasMapping(pNtkNew) )
                pObjNew->pData = pObj->pData;
            else if ( Abc_NtkHasAig(pNtkNew) )
                assert( 0 );
        }
    }
    else if ( Abc_ObjIsNet(pObj) ) // copy the name
        pObjNew->pData = Abc_NtkRegisterName( pNtkNew, pObj->pData );
    else if ( Abc_ObjIsLatch(pObj) ) // copy the reset value
        pObjNew->pData = pObj->pData;
    pObj->pCopy = pObjNew;
    // add the object to the network
    Abc_ObjAdd( pObjNew );
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Creates a new constant node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupConst1( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew )  
{ 
    Abc_Obj_t * pConst1;
    assert( Abc_NtkIsStrash(pNtkAig) );
    assert( Abc_NtkIsSopLogic(pNtkNew) );
    pConst1 = Abc_AigConst1(pNtkAig->pManFunc);
    if ( Abc_ObjFanoutNum(pConst1) > 0 )
        pConst1->pCopy = Abc_NodeCreateConst1( pNtkNew );
    return pConst1->pCopy; 
} 

/**Function*************************************************************

  Synopsis    [Creates a new constant node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupReset( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew )  
{ 
    Abc_Obj_t * pReset, * pConst1;
    assert( Abc_NtkIsStrash(pNtkAig) );
    assert( Abc_NtkIsSopLogic(pNtkNew) );
    pReset = Abc_AigReset(pNtkAig->pManFunc);
    if ( Abc_ObjFanoutNum(pReset) > 0 )
    {
        // create new latch with reset value 0
        pReset->pCopy = Abc_NtkCreateLatch( pNtkNew );
        // add constant node fanin to the latch
        pConst1 = Abc_NodeCreateConst1( pNtkNew );
        Abc_ObjAddFanin( pReset->pCopy, pConst1 );
    }
    return pReset->pCopy; 
} 

/**Function*************************************************************

  Synopsis    [Deletes the object from the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDeleteObj( Abc_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes = pObj->pNtk->vPtrTemp;
    Abc_Ntk_t * pNtk = pObj->pNtk;
    int i;

    assert( !Abc_ObjIsComplement(pObj) );

    // delete fanins and fanouts
    Abc_NodeCollectFanouts( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( vNodes->pArray[i], pObj );
    Abc_NodeCollectFanins( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( pObj, vNodes->pArray[i] );

    // remove from the list of objects
    Vec_PtrWriteEntry( pNtk->vObjs, pObj->Id, NULL );
    pObj->Id = (1<<26)-1;
    pNtk->nObjs--;

    // perform specialized operations depending on the object type
    if ( Abc_ObjIsNet(pObj) )
    {
        // remove the net from the hash table of nets
        if ( pObj->pData && !stmm_delete( pNtk->tName2Net, (char **)&pObj->pData, (char **)&pObj ) )
        {
            printf( "Error: The net is not in the table...\n" );
            assert( 0 );
        }
        pObj->pData = NULL;
        pNtk->nNets--;
    }
    else if ( Abc_ObjIsNode(pObj) )
    {
        if ( Abc_NtkHasBdd(pNtk) )
            Cudd_RecursiveDeref( pNtk->pManFunc, pObj->pData );
        pNtk->nNodes--;
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        pNtk->nLatches--;
    }
    else 
        assert( 0 );
    // recycle the net itself
    Abc_ObjRecycle( pObj );
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
Abc_Obj_t * Abc_NtkFindCo( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNode;
    int i;
    // search the node among COs
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        if ( strcmp( Abc_ObjName(pNode), pName ) == 0 )
            return pNode;
    }
    return NULL;
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
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( stmm_lookup( pNtk->tName2Net, pName, (char**)&pNet ) )
        return pNet;
    return NULL;
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
    pNet->pData = Abc_NtkRegisterName( pNtk, pName );
    Abc_ObjAdd( pNet );
    return pNet;
}
    
/**Function*************************************************************

  Synopsis    [Create the new node.]

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

  Synopsis    [Create the new node.]

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

  Synopsis    [Create the new node.]

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

  Synopsis    [Create the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateLatch( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_LATCH );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst0( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    assert( !Abc_NtkHasAig(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 0\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_ReadLogicZero(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadConst0(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst1( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    if ( Abc_NtkHasAig(pNtk) )
        return Abc_AigConst1(pNtk->pManFunc);
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkHasSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pNode->pData = Cudd_ReadOne(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadConst1(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
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
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadInv(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
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
    else if ( Abc_NtkHasMapping(pNtk) )
        pNode->pData = Mio_LibraryReadBuf(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateAnd( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkHasSop(pNtk) )
    {
        char * pSop;
        pSop = Extra_MmFlexEntryFetch( pNtk->pManFunc, vFanins->nSize + 4 );
        for ( i = 0; i < vFanins->nSize; i++ )
            pSop[i] = '1';
        pSop[i++] = ' ';
        pSop[i++] = '1';
        pSop[i++] = '\n';
        pSop[i++] = 0;
        assert( i == vFanins->nSize + 4 );
        pNode->pData = pSop;
    }
    else if ( Abc_NtkHasBdd(pNtk) )
    {
        DdManager * dd = pNtk->pManFunc;
        DdNode * bFunc, * bTemp;
        bFunc = Cudd_ReadOne(dd); Cudd_Ref( bFunc );
        for ( i = 0; i < vFanins->nSize; i++ )
        {
            bFunc = Cudd_bddAnd( dd, bTemp = bFunc, Cudd_bddIthVar(pNtk->pManFunc,i) );  Cudd_Ref( bFunc );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        pNode->pData = bFunc;
    }
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateOr( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkHasSop(pNtk) )
    {
        char * pSop;
        pSop = Extra_MmFlexEntryFetch( pNtk->pManFunc, vFanins->nSize + 4 );
        for ( i = 0; i < vFanins->nSize; i++ )
            pSop[i] = '0';
        pSop[i++] = ' ';
        pSop[i++] = '0';
        pSop[i++] = '\n';
        pSop[i++] = 0;
        assert( i == vFanins->nSize + 4 );
        pNode->pData = pSop;
    }
    else if ( Abc_NtkHasBdd(pNtk) )
    {
        DdManager * dd = pNtk->pManFunc;
        DdNode * bFunc, * bTemp;
        bFunc = Cudd_ReadLogicZero(dd); Cudd_Ref( bFunc );
        for ( i = 0; i < vFanins->nSize; i++ )
        {
            bFunc = Cudd_bddOr( dd, bTemp = bFunc, Cudd_bddIthVar(pNtk->pManFunc,i) );  Cudd_Ref( bFunc );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        pNode->pData = bFunc;
    }
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

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
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Clones the given node but does not assign the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeClone( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pClone, * pFanin;
    int i;
    assert( Abc_ObjIsNode(pNode) );
    pClone = Abc_NtkCreateNode( pNode->pNtk );   
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pClone, pFanin );
    return pClone;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst0( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode));      
    assert(Abc_NodeIsConst(pNode));
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsConst0(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return Abc_ObjNot(pNode) == Abc_AigConst1(pNode->pNtk->pManFunc);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadConst0(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst1( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode));      
    assert(Abc_NodeIsConst(pNode));
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsConst1(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return pNode == Abc_AigConst1(pNode->pNtk->pManFunc);
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadConst1(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsBuf( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode)); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsBuf(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return 0;
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadBuf(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsInv( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode)); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkHasSop(pNtk) )
        return Abc_SopIsInv(pNode->pData);
    if ( Abc_NtkHasBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkHasAig(pNtk) )
        return 0;
    if ( Abc_NtkHasMapping(pNtk) )
        return pNode->pData == Mio_LibraryReadInv(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

