/**CFile****************************************************************

  FileName    [ntlTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Name table manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlTable.c,v 1.3 2008/10/24 14:18:44 mjarvin Exp $]

***********************************************************************/

#include "ntl.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// hashing for strings
static unsigned Ntl_HashString( const char * pName, int TableSize ) 
{
    static int s_Primes[10] = { 
        1291, 1699, 2357, 4177, 5147, 
        5647, 6343, 7103, 7873, 8147
    };
    unsigned i, Key = 0;
    for ( i = 0; pName[i] != '\0'; i++ )
        Key ^= s_Primes[i%10]*pName[i]*pName[i];
    return Key % TableSize;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates memory for the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelCreateNet( Ntl_Mod_t * p, const char * pName )
{
    Ntl_Net_t * pNet;
    int nSize = sizeof(Ntl_Net_t) + strlen(pName) + 1;
    nSize = (nSize / sizeof(char*) + ((nSize % sizeof(char*)) > 0)) * sizeof(char*); // added by Saurabh on Sep 3, 2009
    pNet = (Ntl_Net_t *)Aig_MmFlexEntryFetch( p->pMan->pMemObjs, nSize );
    memset( pNet, 0, sizeof(Ntl_Net_t) );
    strcpy( pNet->pName, pName );
    pNet->NetId = Vec_PtrSize( p->vNets );
    Vec_PtrPush( p->vNets, pNet );
    return pNet;
}

/**Function*************************************************************

  Synopsis    [Allocates memory for the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_ModelCreateNetName( Ntl_Mod_t * p, const char * pName, int Num )
{
    char * pResult;
    char Buffer[1000];
    assert( strlen(pName) < 900 );
    do {
        sprintf( Buffer, "%s%d", pName, Num++ );
    } while ( Ntl_ModelFindNet( p, Buffer ) != NULL );
    pResult = (char *)Aig_MmFlexEntryFetch( p->pMan->pMemObjs, strlen(Buffer) + 1 );
    strcpy( pResult, Buffer );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Resizes the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelTableResize( Ntl_Mod_t * p )
{
    Ntl_Net_t ** pTableNew, ** ppSpot, * pEntry, * pEntry2;
    int nTableSizeNew, Counter, e, clk;
clk = clock();
    // get the new table size
    nTableSizeNew = Aig_PrimeCudd( 3 * p->nTableSize ); 
    // allocate a new array
    pTableNew = ABC_ALLOC( Ntl_Net_t *, nTableSizeNew );
    memset( pTableNew, 0, sizeof(Ntl_Net_t *) * nTableSizeNew );
    // rehash entries 
    Counter = 0;
    for ( e = 0; e < p->nTableSize; e++ )
        for ( pEntry = p->pTable[e], pEntry2 = pEntry? pEntry->pNext : NULL; 
              pEntry; pEntry = pEntry2, pEntry2 = pEntry? pEntry->pNext : NULL )
            {
                ppSpot = pTableNew + Ntl_HashString( pEntry->pName, nTableSizeNew );
                pEntry->pNext = *ppSpot;
                *ppSpot = pEntry;
                Counter++;
            }
    assert( Counter == p->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", p->nTableSize, nTableSizeNew );
//    ABC_PRT( "Time", clock() - clk );
    // replace the table and the parameters
    ABC_FREE( p->pTable );
    p->pTable = pTableNew;
    p->nTableSize = nTableSizeNew;
}

/**Function*************************************************************

  Synopsis    [Finds net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelFindNet( Ntl_Mod_t * p, const char * pName )
{
    Ntl_Net_t * pEnt;
    unsigned Key = Ntl_HashString( pName, p->nTableSize );
    for ( pEnt = p->pTable[Key]; pEnt; pEnt = pEnt->pNext )
        if ( !strcmp( pEnt->pName, pName ) )
            return pEnt;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Deletes net from the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelDeleteNet( Ntl_Mod_t * p, Ntl_Net_t * pNet )
{
    Ntl_Net_t * pEnt, * pPrev;
    unsigned Key = Ntl_HashString( pNet->pName, p->nTableSize );
    for ( pPrev = NULL, pEnt = p->pTable[Key]; pEnt; pPrev = pEnt, pEnt = pEnt->pNext )
        if ( pEnt == pNet )
            break;
    if ( pEnt == NULL )
    {
        printf( "Ntl_ModelDeleteNet(): Net to be deleted is not found in the hash table.\n" );
        return;
    }
    if ( pPrev == NULL )
        p->pTable[Key] = pEnt->pNext;
    else
        pPrev->pNext = pEnt->pNext;
    p->nEntries--;
}

/**Function*************************************************************

  Synopsis    [Inserts net into the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelInsertNet( Ntl_Mod_t * p, Ntl_Net_t * pNet )
{
    unsigned Key = Ntl_HashString( pNet->pName, p->nTableSize );
    assert( Ntl_ModelFindNet( p, pNet->pName ) == NULL );
    pNet->pNext = p->pTable[Key];
    p->pTable[Key] = pNet;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelFindOrCreateNet( Ntl_Mod_t * p, const char * pName )
{
    Ntl_Net_t * pEnt;
    unsigned Key = Ntl_HashString( pName, p->nTableSize );
    for ( pEnt = p->pTable[Key]; pEnt; pEnt = pEnt->pNext )
        if ( !strcmp( pEnt->pName, pName ) )
            return pEnt;
    pEnt = Ntl_ModelCreateNet( p, pName );
    pEnt->pNext = p->pTable[Key];
    p->pTable[Key] = pEnt;
    if ( ++p->nEntries > 2 * p->nTableSize )
        Ntl_ModelTableResize( p );
    return pEnt;
}

/**Function*************************************************************

  Synopsis    [Creates new net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelDontFindCreateNet( Ntl_Mod_t * p, const char * pName )
{
    Ntl_Net_t * pEnt;
    unsigned Key = Ntl_HashString( pName, p->nTableSize );
    pEnt = Ntl_ModelCreateNet( p, pName );
    pEnt->pNext = p->pTable[Key];
    p->pTable[Key] = pEnt;
    if ( ++p->nEntries > 2 * p->nTableSize )
        Ntl_ModelTableResize( p );
    return pEnt;
}

/**Function*************************************************************

  Synopsis    [Assigns numbers to PIs and POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelSetPioNumbers( Ntl_Mod_t * p )
{
    Ntl_Obj_t * pObj;
    int i;
    Ntl_ModelForEachPi( p, pObj, i )
        pObj->iTemp = i;
    Ntl_ModelForEachPo( p, pObj, i )
        pObj->iTemp = i;
}

/**Function*************************************************************

  Synopsis    [Returns -1, 0, +1 (when it is PI, not found, or PO).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelFindPioNumber_old( Ntl_Mod_t * p, int fPiOnly, int fPoOnly, const char * pName, int * pNumber )
{
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i;
    *pNumber = -1;
    pNet = Ntl_ModelFindNet( p, pName );
    if ( pNet == NULL )
        return 0;
    if ( fPiOnly )
    {
        Ntl_ModelForEachPi( p, pObj, i )
        {
            if ( Ntl_ObjFanout0(pObj) == pNet )
            {
                *pNumber = i;
                return -1;
            }
        }
        return 0;
    }
    if ( fPoOnly )
    {
        Ntl_ModelForEachPo( p, pObj, i )
        {
            if ( Ntl_ObjFanin0(pObj) == pNet )
            {
                *pNumber = i;
                return 1;
            }
        }
        return 0;
    }
    Ntl_ModelForEachPo( p, pObj, i )
    {
        if ( Ntl_ObjFanin0(pObj) == pNet )
        {
            *pNumber = i;
            return 1;
        }
    }
    Ntl_ModelForEachPi( p, pObj, i )
    {
        if ( Ntl_ObjFanout0(pObj) == pNet )
        {
            *pNumber = i;
            return -1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns -1, 0, +1 (when it is PI, not found, or PO).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelFindPioNumber( Ntl_Mod_t * p, int fPiOnly, int fPoOnly, const char * pName, int * pNumber )
{
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pTerm;
    *pNumber = -1;
    pNet = Ntl_ModelFindNet( p, pName );
    if ( pNet == NULL )
        return 0;
    if ( fPiOnly )
    {
        pTerm = pNet->pDriver;
        if ( pTerm && Ntl_ObjIsPi(pTerm) )
        {
            *pNumber = pTerm->iTemp;
            return -1;
        }
        return 0;
    }
    if ( fPoOnly )
    {
        pTerm = (Ntl_Obj_t *)pNet->pCopy;
        if ( pTerm && Ntl_ObjIsPo(pTerm) )
        {
            *pNumber = pTerm->iTemp;
            return 1;
        }
        return 0;
    }
    pTerm = (Ntl_Obj_t *)pNet->pCopy;
    if ( pTerm && Ntl_ObjIsPo(pTerm) )
    {
        *pNumber = pTerm->iTemp;
        return 1;
    }
    pTerm = pNet->pDriver;
    if ( pTerm && Ntl_ObjIsPi(pTerm) )
    {
        *pNumber = pTerm->iTemp;
        return -1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sets the driver of the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelSetNetDriver( Ntl_Obj_t * pObj, Ntl_Net_t * pNet )
{
    if ( pObj->pFanio[pObj->nFanins] != NULL )
        return 0;
    if ( pNet->pDriver != NULL )
        return 0;
    pObj->pFanio[pObj->nFanins] = pNet;
    pNet->pDriver = pObj;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Clears the driver of the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelClearNetDriver( Ntl_Obj_t * pObj, Ntl_Net_t * pNet )
{
    if ( pObj->pFanio[pObj->nFanins] == NULL )
        return 0;
    if ( pNet->pDriver == NULL )
        return 0;
    pObj->pFanio[pObj->nFanins] = NULL;
    pNet->pDriver = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts the number of nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCountNets( Ntl_Mod_t * p )
{
    Ntl_Net_t * pNet;
    int i, Counter = 0;
    Ntl_ModelForEachNet( p, pNet, i )
        Counter++;
    return Counter;
}




/**Function*************************************************************

  Synopsis    [Resizes the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManModelTableResize( Ntl_Man_t * p )
{
    Ntl_Mod_t ** pModTableNew, ** ppSpot, * pEntry, * pEntry2;
    int nModTableSizeNew, Counter, e, clk;
clk = clock();
    // get the new table size
    nModTableSizeNew = Aig_PrimeCudd( 3 * p->nModTableSize ); 
    // allocate a new array
    pModTableNew = ABC_ALLOC( Ntl_Mod_t *, nModTableSizeNew );
    memset( pModTableNew, 0, sizeof(Ntl_Mod_t *) * nModTableSizeNew );
    // rehash entries 
    Counter = 0;
    for ( e = 0; e < p->nModTableSize; e++ )
        for ( pEntry = p->pModTable[e], pEntry2 = pEntry? pEntry->pNext : NULL; 
              pEntry; pEntry = pEntry2, pEntry2 = pEntry? pEntry->pNext : NULL )
            {
                ppSpot = pModTableNew + Ntl_HashString( pEntry->pName, nModTableSizeNew );
                pEntry->pNext = *ppSpot;
                *ppSpot = pEntry;
                Counter++;
            }
    assert( Counter == p->nModEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", p->nTableSize, nTableSizeNew );
//    ABC_PRT( "Time", clock() - clk );
    // replace the table and the parameters
    ABC_FREE( p->pModTable );
    p->pModTable = pModTableNew;
    p->nModTableSize = nModTableSizeNew;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManAddModel( Ntl_Man_t * p, Ntl_Mod_t * pModel )
{
    Ntl_Mod_t * pEnt;
    unsigned Key = Ntl_HashString( pModel->pName, p->nModTableSize );
    for ( pEnt = p->pModTable[Key]; pEnt; pEnt = pEnt->pNext )
        if ( !strcmp( pEnt->pName, pModel->pName ) )
            return 0;
    pModel->pNext = p->pModTable[Key];
    p->pModTable[Key] = pModel;
    if ( ++p->nModEntries > 2 * p->nModTableSize )
        Ntl_ManModelTableResize( p );
    Vec_PtrPush( p->vModels, pModel );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Mod_t * Ntl_ManFindModel( Ntl_Man_t * p, const char * pName )
{
    Ntl_Mod_t * pEnt;
    unsigned Key = Ntl_HashString( pName, p->nModTableSize );
    for ( pEnt = p->pModTable[Key]; pEnt; pEnt = pEnt->pNext )
        if ( !strcmp( pEnt->pName, pName ) )
            return pEnt;
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

