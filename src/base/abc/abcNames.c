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
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
    int Counter;

    // check if the object is in the lookup table
//    if ( stmm_lookup( pObj->pNtk->tObj2Name, (char *)pObj, &pName ) )
//        return pName;
    if ( pName = Nm_ManFindNameById(pObj->pNtk->pManName, pObj->Id) )
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
        {
            sprintf( Buffer, "[%d]", pObj->Id ); // make sure this name is unique!!!
            for ( Counter = 1; Nm_ManFindIdByName(pObj->pNtk->pManName, Buffer, NULL) >= 0; Counter++ )
                sprintf( Buffer, "[%d]_%d", pObj->Id, Counter );
        }
    }
    else
    {
        // in a logic network, PI/PO/latch names are stored in the hash table
        // internal nodes have made up names
        assert( Abc_ObjIsNode(pObj) || Abc_ObjIsLatch(pObj) );
        sprintf( Buffer, "[%d]", pObj->Id );
        for ( Counter = 1; Nm_ManFindIdByName(pObj->pNtk->pManName, Buffer, NULL) >= 0; Counter++ )
            sprintf( Buffer, "[%d]_%d", pObj->Id, Counter );
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

  Synopsis    [Returns the dummy PI name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjNameDummy( char * pPrefix, int Num, int nDigits )
{
    static char Buffer[100];
    sprintf( Buffer, "%s%0*d", pPrefix, nDigits, Num );
    return Buffer;
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
    return Nm_ManStoreIdName( pObjNew->pNtk->pManName, pObjNew->Id, pNameOld, NULL );
}

/**Function*************************************************************

  Synopsis    [Adds new name to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_NtkLogicStoreNamePlus( Abc_Obj_t * pObjNew, char * pNameOld, char * pSuffix )
{
    return Nm_ManStoreIdName( pObjNew->pNtk->pManName, pObjNew->Id, pNameOld, pSuffix );
}

/**Function*************************************************************

  Synopsis    [Duplicates the name arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupCioNamesTable( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj, * pTerm;
    int i, k;
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkAssertNum(pNtk) == Abc_NtkAssertNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    assert( Nm_ManNumEntries(pNtk->pManName) > 0 );
    assert( Nm_ManNumEntries(pNtkNew->pManName) == 0 );
    // copy the CI/CO names if given
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i),      Abc_ObjName(Abc_ObjFanout0Ntk(pObj)) );
    Abc_NtkForEachPo( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkPo(pNtkNew,i),      Abc_ObjName(Abc_ObjFanin0Ntk(pObj)) );
    Abc_NtkForEachAssert( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkAssert(pNtkNew,i),  Abc_ObjName(Abc_ObjFanin0Ntk(pObj)) );
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pTerm, k )
            Abc_NtkLogicStoreName( pTerm->pCopy,          Abc_ObjName(Abc_ObjFanin0Ntk(pTerm)) );
        Abc_ObjForEachFanout( pObj, pTerm, k )
            Abc_NtkLogicStoreName( pTerm->pCopy,          Abc_ObjName(Abc_ObjFanout0Ntk(pTerm)) );
    }
    if ( !Abc_NtkIsSeq(pNtk) )
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkLatch(pNtkNew,i),   Abc_ObjName(Abc_ObjFanout0Ntk(pObj)) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the name arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupCioNamesTableNoLatches( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkAssertNum(pNtk) == Abc_NtkAssertNum(pNtkNew) );
    assert( Nm_ManNumEntries(pNtk->pManName) > 0 );
    assert( Nm_ManNumEntries(pNtkNew->pManName) == 0 );
    // copy the CI/CO names if given
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i),      Abc_ObjName(Abc_ObjFanout0Ntk(pObj)) );
    Abc_NtkForEachPo( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkPo(pNtkNew,i),      Abc_ObjName(Abc_ObjFanin0Ntk(pObj)) );
    Abc_NtkForEachAssert( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkAssert(pNtkNew,i),  Abc_ObjName(Abc_ObjFanin0Ntk(pObj)) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the name arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupCioNamesTableDual( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) * 2 == Abc_NtkPoNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    assert( Nm_ManNumEntries(pNtk->pManName) > 0 );
    assert( Nm_ManNumEntries(pNtkNew->pManName) == 0 );
    // copy the CI/CO names if given
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i),    Abc_ObjName(pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i ) 
    {
        Abc_NtkLogicStoreNamePlus( Abc_NtkPo(pNtkNew,2*i+0),    Abc_ObjName(pObj), "_pos" );
        Abc_NtkLogicStoreNamePlus( Abc_NtkPo(pNtkNew,2*i+1),    Abc_ObjName(pObj), "_neg" );
    }
    Abc_NtkForEachAssert( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkAssert(pNtkNew,i),  Abc_ObjName(pObj) );
    if ( !Abc_NtkIsSeq(pNtk) )
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
        Vec_PtrPush( vNodes, Extra_UtilStrsav(Abc_ObjName(pFanin)) );
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
        Vec_PtrPush( vNames, Extra_UtilStrsav(Buffer) );
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
    qsort( (void *)Vec_PtrArray(pNtk->vPis), Vec_PtrSize(pNtk->vPis), sizeof(Abc_Obj_t *), 
        (int (*)(const void *, const void *)) Abc_NodeCompareNames );
    qsort( (void *)Vec_PtrArray(pNtk->vPos), Vec_PtrSize(pNtk->vPos), sizeof(Abc_Obj_t *), 
        (int (*)(const void *, const void *)) Abc_NodeCompareNames );
    // if the comparison if combinational (latches as PIs/POs), order them too
    if ( fComb )
        qsort( (void *)Vec_PtrArray(pNtk->vLatches), Vec_PtrSize(pNtk->vLatches), sizeof(Abc_Obj_t *), 
            (int (*)(const void *, const void *)) Abc_NodeCompareNames );
    // order CIs/COs first PIs/POs(Asserts) then latches
    Abc_NtkOrderCisCos( pNtk );
    // clean the copy fields
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->pCopy = NULL;
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->pCopy = NULL;
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pCopy = NULL;
}

/**Function*************************************************************

  Synopsis    [Adds dummy names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddDummyPiNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int nDigits, i;
    nDigits = Extra_Base10Log( Abc_NtkPiNum(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjNameDummy("pi", i, nDigits) );
}

/**Function*************************************************************

  Synopsis    [Adds dummy names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddDummyPoNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int nDigits, i;
    nDigits = Extra_Base10Log( Abc_NtkPoNum(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjNameDummy("po", i, nDigits) );
}

/**Function*************************************************************

  Synopsis    [Adds dummy names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddDummyAssertNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int nDigits, i;
    nDigits = Extra_Base10Log( Abc_NtkAssertNum(pNtk) );
    Abc_NtkForEachAssert( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjNameDummy("a", i, nDigits) );
}

/**Function*************************************************************

  Synopsis    [Adds dummy names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddDummyLatchNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int nDigits, i;
    nDigits = Extra_Base10Log( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, Abc_ObjNameDummy("L", i, nDigits) );
}

/**Function*************************************************************

  Synopsis    [Replaces names by short names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShortNames( Abc_Ntk_t * pNtk )
{
    Nm_ManFree( pNtk->pManName );
    pNtk->pManName = Nm_ManCreate( Abc_NtkCiNum(pNtk) + Abc_NtkCoNum(pNtk) - Abc_NtkLatchNum(pNtk) + 10 );
    Abc_NtkAddDummyPiNames( pNtk );
    Abc_NtkAddDummyPoNames( pNtk );
    Abc_NtkAddDummyAssertNames( pNtk );
    Abc_NtkAddDummyLatchNames( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


