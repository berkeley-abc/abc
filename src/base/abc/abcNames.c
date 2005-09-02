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

  Synopsis    [Gets the long name of the object.]

  Description [The temporary name is stored in a static buffer inside this
  procedure. It is important that the name is used before the function is 
  called again!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjName( Abc_Obj_t * pObj )
{
    static char Buffer[500];
    char * pName;

    // check if the object is in the lookup table
    if ( stmm_lookup( pObj->pNtk->tObj2Name, (char *)pObj, &pName ) )
        return pName;

    // consider network types
    if ( Abc_NtkIsNetlist(pObj->pNtk) )
    {
        // in a netlist, nets have names, nodes have no names
        if ( Abc_ObjIsNode(pObj) )
            pObj = Abc_ObjFanout0(pObj);
        assert( Abc_ObjIsNet(pObj) );
        // if the name is not given, invent it
        if ( pObj->pData )
            sprintf( Buffer, "%s", pObj->pData );
        else
            sprintf( Buffer, "[%d]", pObj->Id ); // make sure this name is unique!!!
    }
    else
    {
        // in a logic network, PI/PO/latch names are stored in the hash table
        // internal nodes have made up names
        assert( Abc_ObjIsNode(pObj) || Abc_ObjIsLatch(pObj) );
        sprintf( Buffer, "[%d]", pObj->Id );
    }
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Gets the long name of the node.]

  Description [This name is the output net's name.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjNameSuffix( Abc_Obj_t * pObj, char * pSuffix )
{
    static char Buffer[500];
    sprintf( Buffer, "%s%s", Abc_ObjName(pObj), pSuffix );
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

  Description [The new object (pObjNew) is a PI, PO or latch. The name
  is registered and added to the hash table.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkLogicStoreName( Abc_Obj_t * pObjNew, char * pNameOld )
{
    char * pNewName;
    assert( Abc_ObjIsCio(pObjNew) );
    // get the new name
    pNewName = Abc_NtkRegisterName( pObjNew->pNtk, pNameOld );
    // add the name to the table
    if ( stmm_insert( pObjNew->pNtk->tObj2Name, (char *)pObjNew, pNewName ) )
    {
        assert( 0 ); // the object is added for the second time
    }
    return pNewName;
}

/**Function*************************************************************

  Synopsis    [Adds new name to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkLogicStoreNamePlus( Abc_Obj_t * pObjNew, char * pNameOld, char * pSuffix )
{
    char * pNewName;
    assert( pSuffix );
    assert( Abc_ObjIsCio(pObjNew) );
    // get the new name
    pNewName = Abc_NtkRegisterNamePlus( pObjNew->pNtk, pNameOld, pSuffix );
    // add the name to the table
    if ( stmm_insert( pObjNew->pNtk->tObj2Name, (char *)pObjNew, pNewName ) )
    {
        assert( 0 ); // the object is added for the second time
    }
    return pNewName;
}

/**Function*************************************************************

  Synopsis    [Creates the name arrays from the old network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCreateCioNamesTable( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( st_count(pNtk->tObj2Name) == 0 );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjFanout0(pObj)->pData );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjFanin0(pObj)->pData );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjFanout0(pObj)->pData );
}

/**Function*************************************************************

  Synopsis    [Duplicates the name arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupCioNamesTable( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    assert( st_count(pNtk->tObj2Name) > 0 );
    assert( st_count(pNtkNew->tObj2Name) == 0 );
    // copy the CI/CO names if given
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i),    Abc_ObjName(pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkPo(pNtkNew,i),    Abc_ObjName(pObj) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkLatch(pNtkNew,i), Abc_ObjName(pObj) );
}

/**Function*************************************************************

  Synopsis    [Gets fanin node names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeGetFaninNames( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pFanin;
    int i;
    vNodes = Vec_PtrAlloc( 100 );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Vec_PtrPush( vNodes, util_strsav(Abc_ObjName(pFanin)) );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Gets fanin node names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeGetFakeNames( int nNames )
{
    Vec_Ptr_t * vNames;
    char Buffer[5];
    int i;

    vNames = Vec_PtrAlloc( nNames );
    for ( i = 0; i < nNames; i++ )
    {
        if ( nNames < 26 )
        {
            Buffer[0] = 'a' + i;
            Buffer[1] = 0;
        }
        else
        {
            Buffer[0] = 'a' + i%26;
            Buffer[1] = '0' + i/26;
            Buffer[2] = 0;
        }
        Vec_PtrPush( vNames, util_strsav(Buffer) );
    }
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Gets fanin node names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeFreeNames( Vec_Ptr_t * vNames )
{
    int i;
    if ( vNames == NULL )
        return;
    for ( i = 0; i < vNames->nSize; i++ )
        free( vNames->pArray[i] );
    Vec_PtrFree( vNames );
}

/**Function*************************************************************

  Synopsis    [Collects the CI or CO names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char ** Abc_NtkCollectCioNames( Abc_Ntk_t * pNtk, int fCollectCos )
{
    Abc_Obj_t * pObj;
    char ** ppNames;
    int i;
    if ( fCollectCos )
    {
        ppNames = ALLOC( char *, Abc_NtkCoNum(pNtk) );
        Abc_NtkForEachCo( pNtk, pObj, i )
            ppNames[i] = Abc_ObjName(pObj);
    }
    else
    {
        ppNames = ALLOC( char *, Abc_NtkCiNum(pNtk) );
        Abc_NtkForEachCi( pNtk, pObj, i )
            ppNames[i] = Abc_ObjName(pObj);
    }
    return ppNames;
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeCompareNames( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    int Diff = strcmp( (char *)(*pp1)->pCopy, (char *)(*pp2)->pCopy );
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Orders PIs/POs/latches alphabetically.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkOrderObjsByName( Abc_Ntk_t * pNtk, int fComb )
{
    Abc_Obj_t * pObj;
    int i;
    // temporarily store the names in the copy field
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Abc_ObjName(pObj);
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Abc_ObjName(pObj);
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Abc_ObjName(pObj);
    // order objects alphabetically
    qsort( pNtk->vCis->pArray, pNtk->nPis, sizeof(Abc_Obj_t *), 
        (int (*)(const void *, const void *)) Abc_NodeCompareNames );
    qsort( pNtk->vCos->pArray, pNtk->nPos, sizeof(Abc_Obj_t *), 
        (int (*)(const void *, const void *)) Abc_NodeCompareNames );
    // if the comparison if combinational (latches as PIs/POs), order them too
    if ( fComb )
    {
        qsort( pNtk->vLats->pArray, pNtk->nLatches, sizeof(Abc_Obj_t *), 
            (int (*)(const void *, const void *)) Abc_NodeCompareNames );
        // add latches to make COs
        Abc_NtkForEachLatch( pNtk, pObj, i )
        {
            Vec_PtrWriteEntry( pNtk->vCis, pNtk->nPis + i, pObj );
            Vec_PtrWriteEntry( pNtk->vCos, pNtk->nPos + i, pObj );
        }
    }
    // clean the copy fields
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->pCopy = NULL;
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->pCopy = NULL;
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pCopy = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShortNames( Abc_Ntk_t * pNtk )
{
    stmm_table * tObj2NameNew;
    Abc_Obj_t * pObj;
    char Buffer[100];
    char * pNameNew;
    int Length, i;

    tObj2NameNew = stmm_init_table(stmm_ptrcmp, stmm_ptrhash);
    // create new names and add them to the table
    Length = Extra_Base10Log( Abc_NtkPiNum(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        sprintf( Buffer, "pi%0*d", Length, i );
        pNameNew = Abc_NtkRegisterName( pNtk, Buffer );
        stmm_insert( tObj2NameNew, (char *)pObj, pNameNew );
    }
    // create new names and add them to the table
    Length = Extra_Base10Log( Abc_NtkPoNum(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        sprintf( Buffer, "po%0*d", Length, i );
        pNameNew = Abc_NtkRegisterName( pNtk, Buffer );
        stmm_insert( tObj2NameNew, (char *)pObj, pNameNew );
    }
    // create new names and add them to the table
    Length = Extra_Base10Log( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        sprintf( Buffer, "lat%0*d", Length, i );
        pNameNew = Abc_NtkRegisterName( pNtk, Buffer );
        stmm_insert( tObj2NameNew, (char *)pObj, pNameNew );
    }
    stmm_free_table( pNtk->tObj2Name );
    pNtk->tObj2Name = tObj2NameNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


