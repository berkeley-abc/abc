/**CFile****************************************************************

  FileName    [ntlTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Name table manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlTable.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// hashing for strings
static unsigned Ntl_HashString( char * pName, int TableSize ) 
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
Ntl_Net_t * Ntl_ModelCreateNet( Ntl_Mod_t * p, char * pName )
{
    Ntl_Net_t * pNet;
    pNet = (Ntl_Net_t *)Aig_MmFlexEntryFetch( p->pMan->pMemObjs, sizeof(Ntl_Net_t) + strlen(pName) + 1 );
    memset( pNet, 0, sizeof(Ntl_Net_t) );
    strcpy( pNet->pName, pName );
    return pNet;
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
    pTableNew = ALLOC( Ntl_Net_t *, nTableSizeNew );
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
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( p->pTable );
    p->pTable = pTableNew;
    p->nTableSize = nTableSizeNew;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelFindNet( Ntl_Mod_t * p, char * pName )
{
    Ntl_Net_t * pEnt;
    unsigned Key = Ntl_HashString( pName, p->nTableSize );
    for ( pEnt = p->pTable[Key]; pEnt; pEnt = pEnt->pNext )
        if ( !strcmp( pEnt->pName, pName ) )
            return pEnt;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelFindOrCreateNet( Ntl_Mod_t * p, char * pName )
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

  Synopsis    [Finds or creates the net.]

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

  Synopsis    [Returns -1, 0, +1 (when it is PI, not found, or PO).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelFindPioNumber( Ntl_Mod_t * p, char * pName, int * pNumber )
{
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i;
    *pNumber = -1;
    pNet = Ntl_ModelFindNet( p, pName );
    if ( pNet == NULL )
        return 0;
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


