/**CFile****************************************************************

  FileName    [abcNames.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures working with net and node names.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNames.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Registers the name with the string memory manager.]

  Description [This function should be used to register all names
  permanentsly stored with the network. The pointer returned by
  this procedure contains the copy of the name, which should be used
  in all network manipulation procedures.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkRegisterName( Abc_Ntk_t * pNtk, char * pName )
{
    char * pRegName;
    if ( pName == NULL ) return NULL;
    pRegName = Extra_MmFlexEntryFetch( pNtk->pMmNames, strlen(pName) + 1 );
    strcpy( pRegName, pName );
    return pRegName;
}

/**Function*************************************************************

  Synopsis    [Registers the name with the string memory manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkRegisterNamePlus( Abc_Ntk_t * pNtk, char * pName, char * pSuffix )
{
    char * pRegName;
    assert( pName && pSuffix );
    pRegName = Extra_MmFlexEntryFetch( pNtk->pMmNames, strlen(pName) + strlen(pSuffix) + 1 );
    sprintf( pRegName, "%s%s", pName, pSuffix );
    return pRegName;
}

/**Function*************************************************************

  Synopsis    [Returns the hash table of node names.]

  Description [Creates the hash table of names into nodes for the given
  type of nodes. Additionally, sets the node copy pointers to the names.
  Returns NULL if name duplication is detected.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
stmm_table * Abc_NtkLogicHashNames( Abc_Ntk_t * pNtk, int Type, int fComb )
{
    stmm_table * tNames;
    int i, Limit;
    tNames = stmm_init_table( strcmp, stmm_strhash );
    if ( Type == 0 ) // PI
    {
        Limit = fComb? Abc_NtkCiNum(pNtk) : Abc_NtkPiNum(pNtk);
        for ( i = 0; i < Limit; i++ )
        {
            if ( stmm_insert( tNames, Abc_NtkNameCi(pNtk,i), (char *)Abc_NtkCi(pNtk,i) ) )
            {
                printf( "Error: The name is already in the table...\n" );
                return NULL;
            }
            Abc_NtkCi(pNtk,i)->pCopy = (Abc_Obj_t *)Abc_NtkNameCi(pNtk,i);
        }
    }
    else if ( Type == 1 ) // PO
    {
        Limit = fComb? Abc_NtkCoNum(pNtk) : Abc_NtkPoNum(pNtk);
        for ( i = 0; i < Limit; i++ )
        {
            if ( stmm_insert( tNames, Abc_NtkNameCo(pNtk,i), (char *)Abc_NtkCo(pNtk,i) ) )
            {
                printf( "Error: The name is already in the table...\n" );
                return NULL;
            }
            Abc_NtkCo(pNtk,i)->pCopy = (Abc_Obj_t *)Abc_NtkNameCo(pNtk,i);
        }
    }
    else if ( Type == 2 ) // latch
    {
        for ( i = 0; i < Abc_NtkLatchNum(pNtk); i++ )
        {
            if ( stmm_insert( tNames, Abc_NtkNameLatch(pNtk,i), (char *)Abc_NtkLatch(pNtk,i) ) )
            {
                printf( "Error: The name is already in the table...\n" );
                return NULL;
            }
            Abc_NtkLatch(pNtk,i)->pCopy = (Abc_Obj_t *)Abc_NtkNameLatch(pNtk,i);
        }
    }
    return tNames;
}

/**Function*************************************************************

  Synopsis    [Transfers the names to the node copy pointers.]

  Description [This procedure is used for writing networks into a file.
  Assumes that the latch input names are created from latch names using
  suffix "_in".]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkLogicTransferNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pDriver, * pFanoutNamed;
    int i;
    // transfer the PI/PO/latch names
    Abc_NtkForEachPi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)Abc_NtkNamePi(pNtk,i);
    Abc_NtkForEachPo( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)Abc_NtkNamePo(pNtk,i);
    Abc_NtkForEachLatch( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)Abc_NtkNameLatch(pNtk,i);
    Abc_NtkForEachNode( pNtk, pNode, i )
        pNode->pCopy = NULL;
    // additionally, transfer the names to the CO drivers if they have unique COs
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pDriver = Abc_ObjFanin0(pNode);
        // skip the drivers already having names
        if ( pDriver->pCopy )
            continue;
        // get the named fanout
        pFanoutNamed = Abc_NodeHasUniqueNamedFanout( pDriver );
        if ( pFanoutNamed == NULL || pFanoutNamed != pNode )
            continue;
        // assign the name;
        assert( pNode == pFanoutNamed );
        pDriver->pCopy = pFanoutNamed->pCopy;
    }
    Abc_NtkForEachLatch( pNtk, pNode, i )
    {
        pDriver = Abc_ObjFanin0(pNode);
        // skip the drivers already having names
        if ( pDriver->pCopy )
            continue;
        // get the named fanout
        pFanoutNamed = Abc_NodeHasUniqueNamedFanout( pDriver );
        if ( pFanoutNamed == NULL || pFanoutNamed != pNode )
            continue;
        // assign the name;
        assert( pNode == Abc_NtkLatch(pNtk,i) );
        pDriver->pCopy = (Abc_Obj_t *)Abc_NtkRegisterName( pNtk, Abc_NtkNameLatchInput(pNtk,i) );
    }
}

/**Function*************************************************************

  Synopsis    [Gets the long name of the node.]

  Description [This name is the output net's name.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkNameLatchInput( Abc_Ntk_t * pNtk, int i )
{
    static char Buffer[500];
    sprintf( Buffer, "%s_in", Abc_NtkNameLatch(pNtk, i) );
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Gets the long name of the node.]

  Description [This name is the output net's name.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjName( Abc_Obj_t * pObj )
{
    static char Buffer[500];
    assert( !Abc_NtkIsSeq(pObj->pNtk) );
    // consider network types
    if ( Abc_NtkIsNetlist(pObj->pNtk) )
    {
        // in a netlist, nets have names, nodes have no names
        assert( Abc_ObjIsNet(pObj) );
        // if the name is not given, invent it
        if ( pObj->pData )
            sprintf( Buffer, "%s", pObj->pData );
        else
            sprintf( Buffer, "[%d]", pObj->Id ); // make sure this name is unique!!!
    }
    else
    {
        // in a logic network, PIs/POs/latches have names, internal nodes have no names
        // (exception: an internal node borrows name from its unique non-complemented CO fanout)
        assert( !Abc_ObjIsNet(pObj) );
        if ( pObj->pCopy )
            sprintf( Buffer, "%s", (char *)pObj->pCopy );
        else
            sprintf( Buffer, "[%d]", pObj->Id );
    }
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Finds a unique name for the node.]

  Description [If the name exists, tries appending numbers to it until 
  it becomes unique.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjNameUnique( Abc_Ntk_t * pNtk, char * pName )
{
    static char Buffer[1000];
    int Counter;
    assert( 0 );
    if ( !stmm_is_member( pNtk->tName2Net, pName ) )
        return pName;
    for ( Counter = 1; ; Counter++ )
    {
        sprintf( Buffer, "%s_%d", pName, Counter );
        if ( !stmm_is_member( pNtk->tName2Net, Buffer ) )
            return Buffer;
    }
    return NULL;
}


/**Function*************************************************************

  Synopsis    [Adds new name to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkLogicStoreName( Abc_Obj_t * pNodeNew, char * pNameOld )
{
    char * pNewName;
    assert( !Abc_ObjIsComplement(pNodeNew) );
    // get the new name
    pNewName = Abc_NtkRegisterName( pNodeNew->pNtk, pNameOld );
    // add the name
    if ( Abc_ObjIsPi(pNodeNew) )
        Vec_PtrPush( pNodeNew->pNtk->vNamesPi, pNewName );
    else if ( Abc_ObjIsPo(pNodeNew) )
        Vec_PtrPush( pNodeNew->pNtk->vNamesPo, pNewName );
    else if ( Abc_ObjIsLatch(pNodeNew) )
    {
        Vec_PtrPush( pNodeNew->pNtk->vNamesLatch, pNewName );
        Vec_PtrPush( pNodeNew->pNtk->vNamesPi, pNewName );
        Vec_PtrPush( pNodeNew->pNtk->vNamesPo, pNewName );
    }
    else
        assert( 0 );
    return pNewName;
}

/**Function*************************************************************

  Synopsis    [Adds new name to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkLogicStoreNamePlus( Abc_Obj_t * pNodeNew, char * pNameOld, char * pSuffix )
{
    char * pNewName;
    assert( !Abc_ObjIsComplement(pNodeNew) );
    assert( pSuffix );
    // get the new name
    pNewName = Abc_NtkRegisterNamePlus( pNodeNew->pNtk, pNameOld, pSuffix );
    // add the name
    if ( Abc_ObjIsPi(pNodeNew) )
        Vec_PtrPush( pNodeNew->pNtk->vNamesPi, pNewName );
    else if ( Abc_ObjIsPo(pNodeNew) )
        Vec_PtrPush( pNodeNew->pNtk->vNamesPo, pNewName );
    else if ( Abc_ObjIsLatch(pNodeNew) )
    {
        Vec_PtrPush( pNodeNew->pNtk->vNamesLatch, pNewName );
        Vec_PtrPush( pNodeNew->pNtk->vNamesPi, pNewName );
        Vec_PtrPush( pNodeNew->pNtk->vNamesPo, pNewName );
    }
    else
        assert( 0 );
    return pNewName;
}

/**Function*************************************************************

  Synopsis    [Creates the name arrays from the old network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCreateNameArrays( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pNet, * pLatch;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsNetlist(pNtkNew) );
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    assert( st_count(pNtkNew->tName2Net) == 0 );
    Abc_NtkForEachPi( pNtk, pNet, i )
        Abc_NtkLogicStoreName( pNtkNew->vPis->pArray[i], pNet->pData );
    Abc_NtkForEachPo( pNtk, pNet, i )
        Abc_NtkLogicStoreName( pNtkNew->vPos->pArray[i], pNet->pData );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Abc_NtkLogicStoreName( pNtkNew->vLatches->pArray[i], Abc_ObjFanout0(pLatch)->pData );
}

/**Function*************************************************************

  Synopsis    [Duplicates the name arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupNameArrays( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj, * pLatch;
    int i;
    assert( !Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsNetlist(pNtkNew) );
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    assert( st_count(pNtkNew->tName2Net) == 0 );
    // copy the CI/CO names if given
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pNtkNew->vPis->pArray[i], pNtk->vNamesPi->pArray[i] );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pNtkNew->vPos->pArray[i], pNtk->vNamesPo->pArray[i] );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Abc_NtkLogicStoreName( pNtkNew->vLatches->pArray[i], pNtk->vNamesLatch->pArray[i] );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


