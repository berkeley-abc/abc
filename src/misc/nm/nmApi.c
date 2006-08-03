/**CFile****************************************************************

  FileName    [nmApi.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Name manager.]

  Synopsis    [APIs of the name manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nmApi.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nmInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the name manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nm_Man_t * Nm_ManCreate( int nSize )
{
    Nm_Man_t * p;
    // allocate the table
    p = ALLOC( Nm_Man_t, 1 );
    memset( p, 0, sizeof(Nm_Man_t) );
    // set the parameters
    p->nSizeFactor   = 4; // determined how much larger the table should be compared to data in it
    p->nGrowthFactor = 4; // determined how much the table grows after resizing
    // allocate and clean the bins
    p->nBins = Cudd_PrimeNm(p->nSizeFactor*nSize);
    p->pBinsI2N = ALLOC( Nm_Entry_t *, p->nBins );
    p->pBinsN2I = ALLOC( Nm_Entry_t *, p->nBins );
    memset( p->pBinsI2N, 0, sizeof(Nm_Entry_t *) * p->nBins );
    memset( p->pBinsN2I, 0, sizeof(Nm_Entry_t *) * p->nBins );
    // start the memory manager
    p->pMem = Extra_MmFlexStart();
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the name manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nm_ManFree( Nm_Man_t * p )
{
    Extra_MmFlexStop( p->pMem, 0 );
    FREE( p->pBinsI2N );
    FREE( p->pBinsN2I );
    FREE( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of objects with names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nm_ManNumEntries( Nm_Man_t * p )
{
    return p->nEntries;
}

/**Function*************************************************************

  Synopsis    [Creates a new entry in the name manager.]

  Description [Returns 1 if the entry with the given object ID
  already exists in the name manager.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Nm_ManStoreIdName( Nm_Man_t * p, int ObjId, char * pName, char * pSuffix )
{
    Nm_Entry_t * pEntry, * pEntry2;
    int RetValue, nEntrySize;
    if ( pEntry = Nm_ManTableLookupId(p, ObjId) )
    {
        if ( strcmp(pEntry->Name, pName) == 0 )
            printf( "Nm_ManStoreIdName(): Entry with the same ID and name already exists.\n" );
        else
            printf( "Nm_ManStoreIdName(): Entry with the same ID and different name already exists.\n" );
        return NULL;
    }
    if ( pSuffix == NULL && (pEntry = Nm_ManTableLookupName(p, pName, &pEntry2)) && pEntry2 )
    {
        printf( "Nm_ManStoreIdName(): Two entries with the same name already exist.\n" );
        return NULL;
    }
    // create the entry
    nEntrySize = sizeof(Nm_Entry_t) + strlen(pName) + (pSuffix?strlen(pSuffix):0) + 1;
    nEntrySize = (nEntrySize / 4 + ((nEntrySize % 4) > 0)) * 4;
    pEntry = (Nm_Entry_t *)Extra_MmFlexEntryFetch( p->pMem, nEntrySize );
    pEntry->ObjId = ObjId;
    sprintf( pEntry->Name, "%s%s", pName, pSuffix? pSuffix : "" );
    // add the entry to the hash table
    RetValue = Nm_ManTableAdd( p, pEntry );
    assert( RetValue == 1 );
    return pEntry->Name;
}

/**Function*************************************************************

  Synopsis    [Creates a new entry in the name manager.]

  Description [Returns 1 if the entry with the given object ID
  already exists in the name manager.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nm_ManDeleteIdName( Nm_Man_t * p, int ObjId )
{
    Nm_Entry_t * pEntry;
    pEntry = Nm_ManTableLookupId(p, ObjId);
    if ( pEntry == NULL )
    {
        printf( "Nm_ManDeleteIdName(): This entry is not in the table.\n" );
        return;
    }
    // remove entry from the table
    Nm_ManTableDelete( p, pEntry );
}


/**Function*************************************************************

  Synopsis    [Finds a unique name for the node.]

  Description [If the name exists, tries appending numbers to it until 
  it becomes unique.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Nm_ManCreateUniqueName( Nm_Man_t * p, int ObjId )
{
    static char NameStr[1000];
    Nm_Entry_t * pEntry;
    int i;
    if ( pEntry = Nm_ManTableLookupId(p, ObjId) )
        return pEntry->Name;
    sprintf( NameStr, "[%d]", ObjId );
    for ( i = 1; Nm_ManTableLookupName(p, NameStr, NULL); i++ )
        sprintf( NameStr, "[%d]_%d", ObjId, i );
    return Nm_ManStoreIdName( p, ObjId, NameStr, NULL );
}

/**Function*************************************************************

  Synopsis    [Returns name of the object if the ID is known.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Nm_ManFindNameById( Nm_Man_t * p, int ObjId )
{
    Nm_Entry_t * pEntry;
    if ( pEntry = Nm_ManTableLookupId(p, ObjId) )
        return pEntry->Name;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Returns ID of the object if its name is known.]

  Description [This procedure may return two IDs because POs and latches 
  may have the same name (the only allowed case of name duplication).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nm_ManFindIdByName( Nm_Man_t * p, char * pName, int * pSecond )
{
    Nm_Entry_t * pEntry, * pEntry2;
    if ( pEntry = Nm_ManTableLookupName(p, pName, &pEntry2) )
    {
        if ( pSecond )
            *pSecond = pEntry2? pEntry2->ObjId : -1;
        return pEntry->ObjId;
    }
    return -1;
}


/**Function*************************************************************

  Synopsis    [Prints distribution of entries in the bins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nm_ManPrintTables( Nm_Man_t * p )
{
    int i, Counter;

    // rehash the entries from the old table
    Counter = 0;
    printf( "Int2Name: " );
    for ( i = 0; i < p->nBins; i++ )
    {
        if ( Counter == 0 && p->pBinsI2N[i] == NULL )
            continue;
        if ( p->pBinsI2N[i] )
            Counter++;
        else
        {
            printf( "%d ", Counter );
            Counter = 0;
        }
    }
    printf( "\n" );

    // rehash the entries from the old table
    Counter = 0;
    printf( "Name2Int: " );
    for ( i = 0; i < p->nBins; i++ )
    {
        if ( Counter == 0 && p->pBinsN2I[i] == NULL )
            continue;
        if ( p->pBinsN2I[i] )
            Counter++;
        else
        {
            printf( "%d ", Counter );
            Counter = 0;
        }
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Return the IDs of objects with names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Nm_ManReturnNameIds( Nm_Man_t * p )
{
    Vec_Int_t * vNameIds;
    int i;
    vNameIds = Vec_IntAlloc( p->nEntries );
    for ( i = 0; i < p->nBins; i++ )
        if ( p->pBinsI2N[i] )
            Vec_IntPush( vNameIds, p->pBinsI2N[i]->ObjId );
    return vNameIds;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


